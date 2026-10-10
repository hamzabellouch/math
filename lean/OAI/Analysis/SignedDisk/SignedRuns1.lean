import OAI.Analysis.SignedDisk.PhysicalCells1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace SignedRuns
open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

structure Run where
  dir : Label
  first : ℕ
  last : ℕ

/-- Completed runs, in reverse chronological order. -/
def closedRuns : List Label → List Run
  | [] => []
  | [_] => []
  | n::old::p => if n = old then closedRuns (old::p)
      else ⟨old,activeStart (old::p),p.length⟩::closedRuns (old::p)

def runs : List Label → List Run
  | [] => []
  | n::p => ⟨n,activeStart (n::p),p.length⟩::closedRuns (n::p)

lemma closedRuns_bounds (n : Label) (p : List Label) :
    ∀ a ∈ closedRuns (n::p), a.first ≤ a.last ∧ a.last < p.length := by
  induction p generalizing n with
  | nil => simp [closedRuns]
  | cons old p ih =>
    simp only [closedRuns]
    split_ifs with h
    · intro a ha
      exact ⟨(ih old a ha).1,(ih old a ha).2.trans (by simp)⟩
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact ⟨activeStart_le old p,by simp⟩
      · exact ⟨(ih old a ha).1,(ih old a ha).2.trans (by simp)⟩

lemma runs_bounds (n : Label) (p : List Label) :
    ∀ a ∈ runs (n::p), a.first ≤ a.last ∧ a.last ≤ p.length := by
  intro a ha
  rcases List.mem_cons.mp ha with ha | ha
  · subst a
    exact ⟨activeStart_le n p,le_rfl⟩
  · exact ⟨(closedRuns_bounds n p a ha).1,(closedRuns_bounds n p a ha).2.le⟩

lemma runs_cover (n : Label) (p : List Label) (k : ℕ) (hk : k ≤ p.length) :
    ∃ a ∈ runs (n::p), a.first ≤ k ∧ k ≤ a.last := by
  induction p generalizing n k with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨⟨n,0,0⟩,by simp [runs,activeStart],le_rfl,le_rfl⟩
  | cons old p ih =>
    by_cases h : n = old
    · subst n
      by_cases hs : activeStart (old::p) ≤ k
      · refine ⟨⟨old,activeStart (old::p),p.length+1⟩,?_,hs,?_⟩
        · simp [runs,activeStart]
        · simpa using hk
      · have hk' : k ≤ p.length := (le_of_not_ge hs).trans (activeStart_le old p)
        obtain ⟨a,ha,hak,hka⟩ := ih old k hk'
        have hac : a ∈ closedRuns (old::p) := by
          rcases List.mem_cons.mp ha with ha | ha
          · subst a
            exact False.elim (hs hak)
          · exact ha
        exact ⟨a,by simp [runs,closedRuns,hac],hak,hka⟩
    · by_cases hk' : k ≤ p.length
      · obtain ⟨a,ha,hak,hka⟩ := ih old k hk'
        exact ⟨a,by simpa only [runs,closedRuns,h,ite_false,List.mem_cons] using Or.inr ha,hak,hka⟩
      · have he : k = p.length+1 := by simp only [List.length_cons] at hk; omega
        subst k
        exact ⟨⟨n,p.length+1,p.length+1⟩,by simp [runs,activeStart,h],le_rfl,le_rfl⟩

lemma potential_eq_runs (g : ℂ → ℝ) (r : ℕ → ℝ) (x : ℂ) (n : Label) (p : List Label) :
    potential g r x (n::p) = ((runs (n::p)).map fun a =>
      (runEnvelope g r a.first a.last x-signedAverage g x (r a.first)) • (a.dir:ℂ)).sum := by
  induction p generalizing n with
  | nil => simp [potential,runs,closedRuns,activeStart]
  | cons old p ih =>
    rw [potential,ih]
    by_cases h : n = old
    · subst n
      simp only [runs,closedRuns,activeStart,ite_true,List.length_cons,List.map_cons,List.sum_cons]
      module
    · simp only [runs,closedRuns,activeStart,h,ite_false,List.length_cons,List.map_cons,List.sum_cons]
      abel

lemma radius_in_bin (r : ℕ → ℝ)
    (hstep : ∀ k, 2*r (k+1) = r k) (j : ℕ) {t : ℝ} (ht : t ∈ Icc (r j) (2*r 0)) :
    ∃ k ≤ j, t ∈ Icc (r k) (2*r k) := by
  induction j with
  | zero => exact ⟨0,le_rfl,ht⟩
  | succ j ih =>
    by_cases h : r j ≤ t
    · obtain ⟨k,hk,hkt⟩ := ih ⟨h,ht.2⟩
      exact ⟨k,hk.trans (Nat.le_succ j),hkt⟩
    · exact ⟨j+1,le_rfl,ht.1,by linarith [hstep j]⟩

lemma runs_cover_radius (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hstep : ∀ k, 2*r (k+1) = r k) (n : Label) (p : List Label) {t : ℝ}
    (ht : t ∈ Icc (r p.length) (2*r 0)) :
    ∃ a ∈ runs (n::p), t ∈ Icc (r a.last) (2*r a.first) := by
  obtain ⟨k,hk,hkt⟩ := radius_in_bin r hstep p.length ht
  obtain ⟨a,ha,hi,hj⟩ := runs_cover n p k hk
  refine ⟨a,ha,?_,?_⟩
  · exact (radius_antitone r hr hstep hj).trans hkt.1
  · have hh := radius_antitone r hr hstep hi
    linarith [hkt.2]

/-- Every history has an actually attaining winning run. No radius selection
is differentiated. -/
lemma winning_run (g : ℂ → ℝ) (r : ℕ → ℝ) (hg : ContDiff ℝ 1 g)
    (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (n : Label) (p : List Label) (x : ℂ) :
    ∃ a ∈ runs (n::p), ∃ t ∈ Icc (r a.last) (2*r a.first),
      runEnvelope g r 0 p.length x = signedAverage g x t ∧
      runEnvelope g r a.first a.last x = signedAverage g x t := by
  obtain ⟨t,ht,he,hmax⟩ := runEnvelope_attains g r hg hr hstep (Nat.zero_le _) x
  obtain ⟨a,ha,hat⟩ := runs_cover_radius r hr hstep n p ht
  refine ⟨a,ha,t,hat,he,le_antisymm ?_ ?_⟩
  · obtain ⟨s,hs,hsval,_⟩ := runEnvelope_attains g r hg hr hstep (runs_bounds n p a ha).1 x
    rw [hsval]
    apply hmax
    constructor
    · exact (radius_antitone r hr hstep (runs_bounds n p a ha).2).trans hs.1
    · have hh := radius_antitone r hr hstep (Nat.zero_le a.first)
      linarith [hs.2]
  · exact le_envelope (u := fun t y => signedAverage g y t) hat x (signedAverage_radius_continuousOn hg x (hr a.last))

end SignedRuns

namespace FiniteLabels
lemma Law.ext_mass {ι : Type*} [Fintype ι] {μ ν : Law ι} (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl
end FiniteLabels

namespace SignedAssembly
open Finset FiniteLabels
variable {ι : Type*} [Fintype ι]

/-- The zero row-sum is obtained by differentiating the actual stochastic
partition of unity, not postulated for the row derivatives. -/
def RowJet.ofLawAt (P : ℂ → Law ι) (x : ℂ)
    (hd : ∀ i, DifferentiableAt ℝ (fun y => P y i) x) : RowJet ι ℂ where
  law := P x
  grad i := gradient (fun y => P y i) x
  total_grad := by
    have ht : (fun y => ∑ i, P y i) = fun _ => (1:ℝ) := funext fun y => (P y).total
    have hs : (∑ i, fderiv ℝ (fun y => P y i) x) = 0 := by
      rw [← fderiv_fun_sum (fun i _ => hd i),ht]
      exact fderiv_const_apply (1:ℝ)
    simp only [gradient,← _root_.map_sum,hs,map_zero]
end SignedAssembly

namespace ActualLabels
open FiniteLabels SignedAssembly Finset ConeCoordinates

/-- Observation time zero is the true initial spatial row. Subsequent times
are the true state-dependent spatial switch rows. -/
def observation (h : ℂ → ℂ) (r : ℕ → ℝ) : ℕ → ℂ → Label → Law Label
  | 0,x,_ => initial h (r 0) x
  | k+1,x,n => row h (r (k+1)) x n

def before (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) : ℕ → Law Label
  | 0 => delta old
  | k+1 => marginal h r k x

lemma before_move (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (k : ℕ) :
    before h r old x (k+1) = move (before h r old x k) (observation h r k x) := by
  cases k with
  | zero =>
    apply Law.ext_mass
    funext j
    change initial h (r 0) x j = ∑ n, delta old n*initial h (r 0) x j
    rw [← sum_mul,(delta old).total,one_mul]
  | succ k => rfl

lemma observation_lipschitz (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (n j : Label) : LipschitzWith (Real.toNNReal (16/r k)) (fun x => observation h r k x n j) := by
  cases k with
  | zero =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz (quantize 1 (by norm_num))
      (target h (r 0)) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl) hr
      (by norm_num : (0:ℝ) ≤ 1) (fun _ => le_rfl) j
  | succ k =>
    simpa only [mul_one,observation,initial,row] using spatialRow_component_lipschitz n (target h (r (k+1)))
      (switchChance h (r (k+1)) n) (switchChance_nonneg h (r (k+1)) n)
      (switchChance_le_one h (r (k+1)) n) hr (by norm_num : (0:ℝ) ≤ 1)
      (switchChance_le_one h (r (k+1)) n) j

lemma observation_ae_diff (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) :
    ∀ᵐ x, ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x := by
  simp only [ae_all_iff]
  intro k n j
  exact (observation_lipschitz h r k (hr k) n j).ae_differentiableAt

def observationJet (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (k : ℕ) (n : Label) : RowJet Label ℂ :=
  RowJet.ofLawAt (fun y => observation h r k y n) x (hd k n)

/-- The jet's expected absolute row derivative is exactly T_k/r_k from the
physical spatial packing theorem. -/
lemma observationJet_cost (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (k : ℕ) (hr : 0 < r k) :
    expect (before h r old x k) (fun n => ∑ j, ‖(observationJet h r x hd k n).grad j‖) =
      derivativeCost h r x k/r k := by
  cases k with
  | zero =>
    change expect (delta old) (fun _ => ∑ j, ‖gradient (fun y => initial h (r 0) y j) x‖) = _
    rw [FiniteLabels.expect_const,derivativeCost,mul_div_cancel_left₀ _ hr.ne']
  | succ k =>
    simp only [observationJet,RowJet.ofLawAt,observation,before,derivativeCost,rowDerivative,FiniteLabels.expect]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro n _
    field_simp
end ActualLabels

namespace SignedRuns
open ActualLabels FiniteLabels SignedAssembly Finset

def weight (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) : List Label → ℝ
  | [] => 1
  | n::p => weight h r old x p*observation h r p.length x (p.headD old) n

lemma weight_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (p : List Label) :
    0 ≤ weight h r old x p := by
  induction p with
  | nil => exact zero_le_one
  | cons n p ih => exact mul_nonneg ih ((observation h r p.length x (p.headD old)).nonneg n)

lemma weight_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ) (p : List Label) :
    weight h r old x p ≤ 1 := by
  induction p with
  | nil => exact le_rfl
  | cons n p ih =>
    apply (mul_le_mul ih (law_le_one (observation h r p.length x (p.headD old)) n)
      ((observation h r p.length x (p.headD old)).nonneg n) zero_le_one).trans_eq
    exact one_mul 1

lemma lipschitz_bounded_mul {f g : ℂ → ℝ} {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hg : LipschitzWith L g) (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  rw [lipschitzWith_iff_norm_sub_le] at hf hg ⊢
  intro x y
  calc
    ‖f x*g x-f y*g y‖ = ‖f x*(g x-g y)+g y*(f x-f y)‖ := by congr 1; ring
    _ ≤ ‖f x*(g x-g y)‖+‖g y*(f x-f y)‖ := norm_add_le _ _
    _ = ‖f x‖*‖g x-g y‖+‖g y‖*‖f x-f y‖ := by rw [norm_mul,norm_mul]
    _ ≤ 1*((L:ℝ)*‖x-y‖)+1*((K:ℝ)*‖x-y‖) := by
      gcongr
      · exact hfb x
      · exact hg x y
      · exact hgb y
      · exact hf x y
    _ = ((K+L:ℝ≥0):ℝ)*‖x-y‖ := by push_cast; ring

lemma weight_lipschitz (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (old : Label) (p : List Label) : ∃ K, LipschitzWith K (fun x => weight h r old x p) := by
  induction p with
  | nil => exact ⟨0,LipschitzWith.const 1⟩
  | cons n p ih =>
    obtain ⟨K,hK⟩ := ih
    refine ⟨_,lipschitz_bounded_mul hK (observation_lipschitz h r p.length (hr _) _ n) ?_ ?_⟩
    · intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg h r old x p)]
      exact weight_le_one h r old x p
    · intro x
      rw [Real.norm_eq_abs,abs_of_nonneg ((observation h r p.length x (p.headD old)).nonneg n)]
      exact law_le_one (observation h r p.length x (p.headD old)) n

lemma weight_diff (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (p : List Label) : DifferentiableAt ℝ (fun y => weight h r old y p) x := by
  induction p with
  | nil => exact differentiableAt_const 1
  | cons n p ih => exact ih.mul (hd p.length (p.headD old) n)

lemma gradient_weight_cons (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (n : Label) (p : List Label) :
    gradient (fun y => weight h r old y (n::p)) x =
      weight h r old x p • (observationJet h r x hd p.length (p.headD old)).grad n+
      observation h r p.length x (p.headD old) n • gradient (fun y => weight h r old y p) x := by
  simp only [weight,observationJet,RowJet.ofLawAt,gradient]
  rw [fderiv_fun_mul (weight_diff h r old x hd p) (hd p.length (p.headD old) n)]
  simp only [map_add,map_smul]

def leafSum {E : Type*} [AddCommMonoid E] (f : List Label → E) : ℕ → List Label → E
  | 0,p => f p
  | d+1,p => ∑ n, leafSum f d (n::p)

lemma flux_eq_weightedLeaves (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ) (old : Label)
    (x : ℂ) (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (v : ℕ → ℝ) (d : ℕ) (p : List Label) :
    pathFlux (jet g r x (observationJet h r x hd) v d p (p.headD old))
      (weight h r old x p) (gradient (fun y => weight h r old y p) x) =
        leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    simp only [jet,pathFlux,leafSum]
    apply sum_congr rfl
    intro n _
    change pathFlux _ (weight h r old x (n::p))
      (weight h r old x p • (observationJet h r x hd p.length (p.headD old)).grad n+
        observation h r p.length x (p.headD old) n • gradient (fun y => weight h r old y p) x) = _
    rw [← gradient_weight_cons h r old x hd n p]
    exact ih (n::p)

/-- The signed flux bound for derivatives of the actual spatial history
weights, with the true initial row and forward marginal derivatives. -/
theorem actual_signed_flux_bound (g : ℂ → ℝ) (h : ℂ → ℂ) (r : ℕ → ℝ)
    (hg : ContDiff ℝ 1 g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (old : Label) (x : ℂ)
    (hd : ∀ k n j, DifferentiableAt ℝ (fun y => observation h r k y n j) x)
    (v : ℕ → ℝ)
    (hv : ∀ k t t', 0 < t → t ≤ 4*r k → 0 < t' → t' ≤ 4*r k →
      |DiskMoments.signedAverage g x t-DiskMoments.signedAverage g x t'| ≤ v k)
    (m : ℕ) :
    |leafSum (fun q => inner ℝ (gradient (fun y => weight h r old y q) x) (potential g r x q)) m []| ≤
      ∑ k ∈ range m, (derivativeCost h r x k/r k)*(∑ l ∈ Ico k m, v l) := by
  have hh := run_signed_flux_bound g r x (observationJet h r x hd) v hg hr hstep hv m old
    (before h r old x) rfl (before_move h r old x)
  have he := flux_eq_weightedLeaves g h r old x hd v m []
  simp only [List.headD_nil,weight] at he
  rw [show gradient (fun _ : ℂ => (1:ℝ)) x = 0 from gradient_const x 1] at he
  rw [he] at hh
  simpa only [observationJet_cost h r old x hd _ (hr _)] using hh

open DiskMoments RadiusEnvelope ActualLabels ConeCoordinates

lemma run_gradient_touching {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) {i j : ℕ} {x : ℂ}
    (hd : DifferentiableAt ℝ (runEnvelope g r i j) x) {t : ℝ}
    (ht : t ∈ Icc (r j) (2*r i)) (he : runEnvelope g r i j x = signedAverage g x t) :
    gradient (runEnvelope g r i j) x = gradient (fun y => signedAverage g y t) x := by
  obtain ⟨K,hK⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  have hu := hasFDerivAt_signedAverage hg (fun y => norm_fderiv_le_of_lipschitz ℝ hK) x
    ((hr j).trans_le ht.1)
  unfold gradient runEnvelope
  rw [RadiusEnvelope.fderiv_touching ht (fun y => signedAverage_radius_continuousOn hg y (hr j)) he hd hu.differentiableAt]

lemma runs_ae_diff {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k) :
    ∀ᵐ x, ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x := by
  simp only [ae_all_iff]
  intro i j hij
  have hab : r j ≤ 2*r i := by
    have := radius_antitone r hr hstep hij
    linarith [hr i]
  obtain ⟨L,hL⟩ := run_envelope_lipschitz hg hgc (hr j) hab
  exact hL.ae_differentiableAt

def coneContribution (n : Label) (z : ℂ) : ℝ :=
  inner ℝ (n:ℂ) z+max 0 (-inner ℝ (axis n 1) z)+max 0 (-inner ℝ (axis n (-1)) z)

lemma coneContribution_nonneg (n : Label) (z : ℂ) : 0 ≤ coneContribution n z := by
  have hc := cone_algebra (label_unit n) z
  change ‖z‖ ≤ 12*coneContribution n z at hc
  linarith [norm_nonneg z]

theorem run_master {g : ℂ → ℝ} {r : ℕ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hr : ∀ k, 0 < r k) (hstep : ∀ k, 2*r (k+1) = r k)
    (n : Label) (p : List Label) (x : ℂ)
    (hd : ∀ i j, i ≤ j → DifferentiableAt ℝ (runEnvelope g r i j) x) :
    ‖gradient (runEnvelope g r 0 p.length) x‖ ≤
      12*((runs (n::p)).map fun a => coneContribution a.dir
        (gradient (runEnvelope g r a.first a.last) x)).sum := by
  obtain ⟨a,ha,t,ht,hgval,haval⟩ := winning_run g r hg hr hstep n p x
  have hab := runs_bounds n p a ha
  have htg : t ∈ Icc (r p.length) (2*r 0) := by
    constructor
    · exact (radius_antitone r hr hstep hab.2).trans ht.1
    · have hh := radius_antitone r hr hstep (Nat.zero_le a.first)
      linarith [ht.2]
  have he : gradient (runEnvelope g r 0 p.length) x = gradient (runEnvelope g r a.first a.last) x :=
    (run_gradient_touching hg hgc hr (hd 0 p.length (Nat.zero_le _)) htg hgval).trans
      (run_gradient_touching hg hgc hr (hd a.first a.last hab.1) ht haval).symm
  rw [he]
  apply (cone_algebra (label_unit a.dir) _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 12)
  apply List.single_le_sum
  · intro z hz
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
    exact coneContribution_nonneg b.dir _
  · exact List.mem_map.mpr ⟨a,ha,rfl⟩
end SignedRuns

end SignedDisk

end

end OAI
