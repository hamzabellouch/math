import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.ShellCharging
import OAI.Combinatorics.ThinTrees.Normalization.Realization

namespace OAI

/-! Metric compact charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset

section RadialLaws
variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

def normDistance (q r : J → ℝ) : ℝ := ‖q-r‖

def inPolytope (q : J → ℝ) : Prop := q ∈ polytope

def isProfile (q : J → ℝ) : Prop := ∃ j : J, q = profile j

omit [PseudoMetricSpace J] in
lemma normDistance_self (q : J → ℝ) : normDistance q q = 0 := by
  simp [normDistance]

omit [PseudoMetricSpace J] in
lemma normDistance_comm (q r : J → ℝ) : normDistance q r = normDistance r q :=
  norm_sub_rev _ _

omit [PseudoMetricSpace J] in
lemma normDistance_triangle (q r s : J → ℝ) :
    normDistance q s ≤ normDistance q r + normDistance r s := by
  simpa only [normDistance, dist_eq_norm] using dist_triangle q r s

omit [Fintype J] in
lemma isProfile_inPolytope {q : J → ℝ} (hq : isProfile q) : inPolytope q := by
  obtain ⟨j,rfl⟩ := hq
  exact profile_mem j

omit [PseudoMetricSpace J] in
lemma segment_formula (q r : J → ℝ) (t : ℝ) :
    (fun j => q j+t*(r j-q j)) = mix q r t := by
  ext j
  simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma inPolytope_segment {q r : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    inPolytope (fun j => q j+t*(r j-q j)) := by
  rw [segment_formula]
  exact mix_mem hq hr ht

lemma isProfile_radial_affine {q r c : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    (hc : isProfile c) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    normDistance (fun j => q j+t*(r j-q j)) c =
      normDistance q c+t*(normDistance r c-normDistance q c) := by
  obtain ⟨j,rfl⟩ := hc
  rw [segment_formula]
  change ‖mix q r t-profile j‖ = _
  rw [radius_mix hq hr j ht]
  unfold normDistance
  ring
end RadialLaws

structure RadialShell (V : Type*) where
  center : V
  inner : ℝ
  outer : ℝ
  ordinary : Bool
  deriving DecidableEq

namespace RadialShell
variable {V : Type*} {J : Type*} [Fintype J] [PseudoMetricSpace J]

def ball (v : V) (r : ℝ) : RadialShell V := ⟨v,0,r,true⟩
def hollow (v : V) (a b : ℝ) : RadialShell V := ⟨v,a,b,false⟩
def width (H : RadialShell V) : ℝ := H.outer-H.inner

def support (X : V → J → ℝ) (H : RadialShell V) : Set (J → ℝ) :=
  {w | inPolytope w ∧ normDistance w (X H.center)<H.outer ∧
    (H.ordinary = true ∨ H.inner<normDistance w (X H.center))}

def Valid (X : V → J → ℝ) (H : RadialShell V) : Prop :=
  0 ≤ H.inner ∧ H.inner < H.outer ∧ (H.ordinary = true → H.inner = 0) ∧
  (∃u, normDistance (X u) (X H.center) ≤ H.inner) ∧
  (∃v, H.outer ≤ normDistance (X v) (X H.center))

omit [PseudoMetricSpace J] in
lemma valid_width_pos {X : V → J → ℝ} {H : RadialShell V} (hH : H.Valid X) :
    0 < H.width := sub_pos.mpr hH.2.1

lemma support_ball (X : V → J → ℝ) (v : V) (r : ℝ) :
    (ball v r).support X = {w | inPolytope w ∧ normDistance w (X v)<r} := by
  ext w
  simp [support,ball]

lemma support_hollow (X : V → J → ℝ) (v : V) (a b : ℝ) :
    (hollow v a b).support X = {w | inPolytope w ∧ a<normDistance w (X v) ∧ normDistance w (X v)<b} := by
  ext w
  simp only [support,hollow,Set.mem_ofPred_eq,Bool.false_eq_true,false_or]
  tauto

lemma valid_support_nonempty {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    {H : RadialShell V} (hH : H.Valid X) : (H.support X).Nonempty := by
  obtain ⟨v,hv⟩ := hH.2.2.2.2
  let R := normDistance (X v) (X H.center)
  let q := (H.inner+H.outer)/2
  have hq : H.inner<q ∧ q<H.outer := by dsimp [q]; constructor <;> linarith [hH.2.1]
  have hR : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt hH.1 hH.2.1) hv
  let t := q/R
  have ht : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (le_trans hH.1 hq.1.le) hR.le,
      (div_le_one hR).mpr (le_trans hq.2.le hv)⟩
  let w := fun j => X H.center j+t*(X v j-X H.center j)
  have hw : normDistance w (X H.center) = q := by
    rw [isProfile_radial_affine (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) (hX _) ht,
      normDistance_self, sub_zero, zero_add]
    exact div_mul_cancel₀ _ hR.ne'
  exact ⟨w,inPolytope_segment (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) ht,
    hw ▸ hq.2,Or.inr (hw ▸ hq.1)⟩

omit [PseudoMetricSpace J] in
lemma restriction_valid {X : V → J → ℝ} {H : RadialShell V}
    (hH : H.Valid X) {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) (hab : a < b) :
    (hollow H.center a b).Valid X := by
  refine ⟨hH.1.trans ha,hab,by simp [hollow],?_,?_⟩
  · obtain ⟨u,hu⟩ := hH.2.2.2.1
    exact ⟨u,hu.trans ha⟩
  · obtain ⟨v,hv⟩ := hH.2.2.2.2
    exact ⟨v,hb.trans hv⟩

lemma restriction_subset (X : V → J → ℝ) (H : RadialShell V)
    {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) :
    (hollow H.center a b).support X ⊆ H.support X := by
  intro w hw
  rw [support_hollow] at hw
  exact ⟨hw.1,lt_of_lt_of_le hw.2.2 hb,Or.inr (lt_of_le_of_lt ha hw.2.1)⟩

lemma ball_subset_of_radial_margin (X : V → J → ℝ) (H : RadialShell V)
    (z : V) {δ : ℝ} (hlo : H.inner+δ ≤ normDistance (X z) (X H.center))
    (hhi : normDistance (X z) (X H.center) ≤ H.outer-δ) :
    (ball z δ).support X ⊆ H.support X := by
  intro w hw
  rw [support_ball] at hw
  have htri := normDistance_triangle w (X z) (X H.center)
  have htri' := normDistance_triangle (X z) w (X H.center)
  rw [normDistance_comm (X z) w] at htri'
  exact ⟨hw.1,by linarith [hw.2],Or.inr (by linarith [hw.2])⟩

lemma ball_disjoint_hollow_lower (X : V → J → ℝ) (x z : V) {δ q a : ℝ}
    (hq : q+δ ≤ normDistance (X z) (X x)) :
    Disjoint ((ball z δ).support X) ((hollow x a q).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle (X z) w (X x)
  rw [normDistance_comm (X z) w] at ht
  linarith [hw.2,hz.2.2]

lemma ball_disjoint_hollow_upper (X : V → J → ℝ) (x z : V) {δ q b : ℝ}
    (hq : normDistance (X z) (X x)+δ ≤ q) :
    Disjoint ((ball z δ).support X) ((hollow x q b).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle w (X z) (X x)
  linarith [hw.2,hz.2.1]

lemma concentric_disjoint (X : V → J → ℝ) (x : V) {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint ((hollow x a b).support X) ((hollow x c d).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_hollow] at hw hz
  linarith [hw.2.2,hz.2.1]

lemma disjoint_balls_distance {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    (u v : V) {δ : ℝ} (hd : Disjoint ((ball u δ).support X) ((ball v δ).support X)) :
    2*δ ≤ normDistance (X u) (X v) := by
  by_contra hh
  have hh := not_le.mp hh
  let w := fun j => X u j+(1/2:ℝ)*(X v j-X u j)
  have hw := inPolytope_segment (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v))
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hu := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX u)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hv := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX v)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  simp only [normDistance_self,normDistance_comm (X v) (X u)] at hu hv
  have hwu : w ∈ (ball u δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w]; linarith⟩
  have hwv : w ∈ (ball v δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w]; linarith⟩
  exact Set.disjoint_left.mp hd hwu hwv

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

def Arrangement (X : V → J → ℝ) (O : Finset (RadialShell V)) : Prop :=
  (∀H ∈ O, H.Valid X) ∧ (O : Set (RadialShell V)).Pairwise (fun H K => Disjoint (H.support X) (K.support X))

omit [DecidableEq V] in
lemma arrangement_empty : Arrangement X ∅ := by simp [Arrangement]

omit [DecidableEq V] in
lemma arrangement_subset {O P : Finset (RadialShell V)} (hO : Arrangement X O) (hPO : P ⊆ O) :
    Arrangement X P := ⟨fun H hH => hO.1 H (hPO hH),hO.2.mono hPO⟩

omit [DecidableEq V] in
lemma arrangement_disjoint_finsets (hX : ∀v, isProfile (X v))
    {O P : Finset (RadialShell V)} (hO : Arrangement X O)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Disjoint O P := by
  rw [Finset.disjoint_left]
  intro H hHO hHP
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hO.1 H hHO)
  exact Set.disjoint_left.mp (hd H hHO H hHP) hw hw

lemma arrangement_union {O P : Finset (RadialShell V)}
    (hO : Arrangement X O) (hP : Arrangement X P)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Arrangement X (O ∪ P) := by
  constructor
  · intro H hH
    rcases mem_union.mp hH with hH | hH
    · exact hO.1 H hH
    · exact hP.1 H hH
  · intro H hH K hK hne
    rcases mem_union.mp hH with hH | hH <;> rcases mem_union.mp hK with hK | hK
    · exact hO.2 hH hK hne
    · exact hd H hH K hK
    · exact (hd K hK H hH).symm
    · exact hP.2 hH hK hne

lemma image_restriction_injective (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Set.InjOn f (O : Set (RadialShell V)) := by
  intro H hH K hK heq
  by_contra hne
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hf H hH).1
  exact Set.disjoint_left.mp (hO.2 hH hK hne) ((hf H hH).2 hw)
    ((hf K hK).2 (heq ▸ hw))

lemma arrangement_image_restriction {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Arrangement X (O.image f) := by
  constructor
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := mem_image.mp hH
    exact (hf K hK).1
  · intro H hH K hK hne
    obtain ⟨H',hH',rfl⟩ := mem_image.mp hH
    obtain ⟨K',hK',rfl⟩ := mem_image.mp hK
    exact (hO.2 hH' hK' (by intro heq; exact hne (congrArg f heq))).mono
      (hf H' hH').2 (hf K' hK').2

def capacity (Δ : ℝ) (H : RadialShell V) : ℝ := max (H.width-6*Δ) 0

def potential (Δ : ℝ) (O : Finset (RadialShell V)) : ℝ := ∑H ∈ O, capacity Δ H

omit [DecidableEq V] in
lemma capacity_nonneg (Δ : ℝ) (H : RadialShell V) : 0 ≤ capacity Δ H := le_max_right _ _
omit [DecidableEq V] in
lemma capacity_ge_formal (Δ : ℝ) (H : RadialShell V) : H.width-6*Δ ≤ capacity Δ H := le_max_left _ _

lemma potential_union {O P : Finset (RadialShell V)} (hOP : Disjoint O P) (Δ : ℝ) :
    potential Δ (O ∪ P) = potential Δ O+potential Δ P := sum_union hOP

lemma potential_erase {O : Finset (RadialShell V)} {H : RadialShell V}
    (hH : H ∈ O) (Δ : ℝ) : potential Δ (O.erase H)+capacity Δ H = potential Δ O :=
  sum_erase_add _ _ hH

lemma potential_image_restriction (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) (Δ : ℝ) :
    potential Δ (O.image f) = ∑H ∈ O, capacity Δ (f H) := by
  exact sum_image (fun H hH K hK heq => image_restriction_injective hX hO f hf hH hK heq)

omit [DecidableEq V] in
lemma capacity_ball {δ Δ : ℝ} (h : 6*Δ ≤ δ) (v : V) :
    capacity Δ (ball v δ) = δ-6*Δ := by
  simp only [capacity,width,ball,sub_zero]
  exact max_eq_left (sub_nonneg.mpr h)

omit [DecidableEq V] in
lemma ball_injective (δ : ℝ) : Function.Injective (fun v : V => ball v δ) := by
  intro u v heq
  exact congrArg RadialShell.center heq

lemma potential_balls {δ Δ : ℝ} (h : 6*Δ ≤ δ) (C : Finset V) :
    potential Δ (C.image (fun v => ball v δ)) = (C.card : ℝ)*(δ-6*Δ) := by
  rw [potential,sum_image (fun _ _ _ _ heq => ball_injective δ heq)]
  simp only [capacity_ball h,sum_const,nsmul_eq_mul]

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

omit [DecidableEq V] in
lemma potential_filter_width (O : Finset (RadialShell V)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    potential Δ (O.filter (fun H => 0 < H.width)) = potential Δ O := by
  apply sum_subset (filter_subset _ _)
  intro H hH hn
  have hw : H.width ≤ 0 := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
  exact max_eq_right (by nlinarith)

lemma arrangement_balls {U : Finset V} {δ : ℝ}
    (hv : ∀u ∈ U, (ball u δ).Valid X)
    (hd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))) :
    Arrangement X (U.image (fun v => ball v δ)) := by
  constructor
  · intro H hH
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    exact hv u hu
  · intro H hH K hK hne
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hK
    exact hd hu hv (by intro heq; exact hne (congrArg (fun z => ball z δ) heq))

lemma split_shells (_hX : ∀v, isProfile (X v))
    {H : RadialShell V} (hH : H.Valid X) {L R δ Δ Δ' n : ℝ}
    (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (hL : H.inner+δ ≤ L) (hR : R ≤ H.outer-δ) (hLR : L ≤ R)
    (hspan : R-L ≤ Δ) (hn : 36*Δ ≤ n*δ) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, K.support X ⊆ H.support X) ∧
      (∀z, L ≤ normDistance (X z) (X H.center) → normDistance (X z) (X H.center) ≤ R →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      capacity Δ H+n*δ/4 ≤ potential Δ P+n*(δ-6*Δ') := by
  let A := hollow H.center H.inner (L-δ)
  let B := hollow H.center (R+δ) H.outer
  let P := ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width)
  have hΔ0 : 0 ≤ Δ := by linarith
  have hA : H.inner ≤ L-δ := by linarith
  have hB : R+δ ≤ H.outer := by linarith
  have hAB : A ≠ B := by
    intro heq
    have := congrArg RadialShell.inner heq
    change H.inner = R+δ at this
    linarith
  have hpA : L-δ ≤ H.outer := by linarith
  have hpB : H.inner ≤ R+δ := by linarith
  have hdAB : Disjoint (A.support X) (B.support X) := concentric_disjoint X H.center (by linarith)
  have hv : ∀K ∈ P, K.Valid X := by
    intro K hK
    obtain ⟨hK,hw⟩ := mem_filter.mp hK
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_valid hH le_rfl hpA (by exact sub_pos.mp hw)
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_valid hH hpB le_rfl (by exact sub_pos.mp hw)
  have hsub : ∀K ∈ P, K.support X ⊆ H.support X := by
    intro K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_subset X H le_rfl hpA
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_subset X H hpB le_rfl
  have harr : Arrangement X P := by
    refine ⟨hv,?_⟩
    intro J hJ K hK hne
    have hJ := (mem_filter.mp hJ).1
    have hK := (mem_filter.mp hK).1
    simp only [mem_insert,mem_singleton] at hJ hK
    rcases hJ with rfl | rfl <;> rcases hK with rfl | rfl
    · exact (hne rfl).elim
    · exact hdAB
    · exact hdAB.symm
    · exact (hne rfl).elim
  refine ⟨P,harr,hsub,?_,?_⟩
  · intro z hzL hzR K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact ball_disjoint_hollow_lower X H.center z (by linarith)
    · have heq := mem_singleton.mp hK
      subst K
      exact ball_disjoint_hollow_upper X H.center z (by linarith)
  · have hp : potential Δ P = capacity Δ A+capacity Δ B := by
      rw [show P = ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width) from rfl,
        potential_filter_width _ hΔ0]
      simp [potential,hAB]
    rw [hp]
    have hn0 : 0 ≤ n := by nlinarith
    have hnew : n*δ/2 ≤ n*(δ-6*Δ') := by nlinarith
    have hcapA := capacity_ge_formal Δ A
    have hcapB := capacity_ge_formal Δ B
    have hcapA0 := capacity_nonneg Δ A
    have hcapB0 := capacity_nonneg Δ B
    change L-δ-H.inner-6*Δ ≤ capacity Δ A at hcapA
    change H.outer-(R+δ)-6*Δ ≤ capacity Δ B at hcapB
    by_cases ht : H.width-6*Δ ≤ 0
    · rw [capacity,max_eq_right ht]
      nlinarith
    · rw [capacity,max_eq_left (le_of_not_ge ht)]
      dsimp [width]
      nlinarith

lemma shrink_shells (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, ∃H ∈ O, K.support X ⊆ H.support X) ∧
      (∀z, (∀H ∈ O, ¬(H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
        normDistance (X z) (X H.center) ≤ H.outer-δ-Δ)) →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      potential Δ O ≤ potential Δ' P := by
  let s := 2*δ+Δ
  let f := fun H : RadialShell V => hollow H.center (H.inner+s) (H.outer-s)
  let Q := O.filter (fun H => 2*s < H.width)
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hres : 2*s+6*Δ' ≤ 6*Δ := by dsimp [s]; linarith
  have hQ : Arrangement X Q := arrangement_subset hO (filter_subset _ _)
  have hf : ∀H ∈ Q, (f H).Valid X ∧ (f H).support X ⊆ H.support X := by
    intro H hH
    obtain ⟨hH,hw⟩ := mem_filter.mp hH
    exact ⟨restriction_valid (hO.1 H hH) (by linarith) (by linarith)
      (by dsimp [width] at hw; linarith),restriction_subset X H (by linarith) (by linarith)⟩
  refine ⟨Q.image f,arrangement_image_restriction hQ f hf,?_,?_,?_⟩
  · intro K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    exact ⟨H,(mem_filter.mp hH).1,(hf H hH).2⟩
  · intro z hz K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    have hz := hz H (mem_filter.mp hH).1
    by_cases hlo : H.inner+δ+Δ ≤ normDistance (X z) (X H.center)
    · have hhi : H.outer-δ-Δ < normDistance (X z) (X H.center) :=
        lt_of_not_ge (fun hh => hz ⟨hlo,hh⟩)
      exact ball_disjoint_hollow_lower X H.center z (by dsimp [s]; linarith)
    · have hlo := lt_of_not_ge hlo
      exact ball_disjoint_hollow_upper X H.center z (by dsimp [s]; linarith)
  · rw [potential_image_restriction hX hQ f hf]
    have heq : potential Δ O = potential Δ Q := by
      symm
      apply sum_subset (filter_subset _ _)
      intro H hH hn
      have hw : H.width ≤ 2*s := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
      exact max_eq_right (by linarith)
    rw [heq]
    apply sum_le_sum
    intro H hH
    apply max_le_max_right
    dsimp [f,width,hollow]
    linarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

omit [DecidableEq V] [PseudoMetricSpace J] in
lemma radial_span {D : Finset V} (hD : D.Nonempty) {Δ δ : ℝ}
    (hdiam : ∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ)
    {H : RadialShell V} {z : V} (hz : z ∈ D)
    (hint : H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
      normDistance (X z) (X H.center) ≤ H.outer-δ-Δ) :
    ∃L R : ℝ, H.inner+δ ≤ L ∧ R ≤ H.outer-δ ∧ L ≤ R ∧ R-L ≤ Δ ∧
      (∀u ∈ D, L ≤ normDistance (X u) (X H.center) ∧ normDistance (X u) (X H.center) ≤ R) := by
  obtain ⟨u,hu,humin⟩ := D.exists_min_image (fun v => normDistance (X v) (X H.center)) hD
  obtain ⟨v,hv,hvmax⟩ := D.exists_max_image (fun v => normDistance (X v) (X H.center)) hD
  refine ⟨normDistance (X u) (X H.center),normDistance (X v) (X H.center),?_,?_,?_,?_,?_⟩
  · have ht := normDistance_triangle (X z) (X u) (X H.center)
    have hd := hdiam z hz u hu
    linarith [hint.1]
  · have ht := normDistance_triangle (X v) (X z) (X H.center)
    have hd := hdiam v hv z hz
    linarith [hint.2]
  · exact humin v hv
  · have ht := normDistance_triangle (X v) (X u) (X H.center)
    linarith [hdiam v hv u hu]
  · exact fun w hw => ⟨humin w hw,hvmax w hw⟩

lemma compact_phase (hX : ∀v, isProfile (X v))
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (U : Finset V) (hUv : ∀u ∈ U, (ball u δ).Valid X)
    (hUd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (F : Finset (Finset V))
    (hFd : (F : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀D ∈ F, D ⊆ U ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ) ∧ 36*Δ ≤ (D.card : ℝ)*δ)
    (O : Finset (RadialShell V)) (hO : Arrangement X O)
    (C : Finset V) (hCU : C ⊆ U) (hCF : ∀D ∈ F, Disjoint C D)
    (hOC : ∀H ∈ O, ∀z ∈ C, Disjoint (H.support X) ((ball z δ).support X)) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      potential Δ O+(C.card : ℝ)*(δ-6*Δ')+δ/4*∑D ∈ F, (D.card : ℝ) ≤ potential Δ' Z := by
  induction F using Finset.strongInductionOn generalizing O C with
  | _ F ih =>
    by_cases hinter : ∃D ∈ F, ∃z ∈ D, ∃H ∈ O,
      H.inner+δ+Δ ≤ normDistance (X z) (X H.center) ∧
        normDistance (X z) (X H.center) ≤ H.outer-δ-Δ
    · obtain ⟨D,hDF,z,hz,H,hHO,hint⟩ := hinter
      obtain ⟨L,R,hL,hR,hLR,hspan,hbounds⟩ :=
        radial_span (hF D hDF).2.1 (hF D hDF).2.2.1 hz hint
      obtain ⟨P,hP,hPH,hPD,hpot⟩ := split_shells hX (hO.1 H hHO) hδ hΔ hΔ' hnext
        hL hR hLR hspan (hF D hDF).2.2.2
      have hballH : ∀u ∈ D, (ball u δ).support X ⊆ H.support X := by
        intro u hu
        exact ball_subset_of_radial_margin X H u (hL.trans (hbounds u hu).1)
          ((hbounds u hu).2.trans hR)
      have hcross : ∀K ∈ O.erase H, ∀J ∈ P, Disjoint (K.support X) (J.support X) := by
        intro K hK J hJ
        exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hPH J hJ)
      have hOE := arrangement_subset hO (erase_subset H O)
      have hOP := arrangement_union hOE hP hcross
      have hCUD : C ∪ D ⊆ U := union_subset hCU (hF D hDF).1
      have hCDE : ∀E ∈ F.erase D, Disjoint (C ∪ D) E := by
        intro E hE
        exact disjoint_union_left.mpr ⟨hCF E (mem_of_mem_erase hE),
          hFd hDF (mem_of_mem_erase hE) (ne_of_mem_erase hE).symm⟩
      have hnewOC : ∀K ∈ O.erase H ∪ P, ∀u ∈ C ∪ D,
          Disjoint (K.support X) ((ball u δ).support X) := by
        intro K hK u hu
        rcases mem_union.mp hK with hK | hK <;> rcases mem_union.mp hu with hu | hu
        · exact hOC K (mem_of_mem_erase hK) u hu
        · exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hballH u hu)
        · exact (hOC H hHO u hu).mono_left (hPH K hK)
        · exact (hPD u (hbounds u hu).1 (hbounds u hu).2 K hK).symm
      obtain ⟨Z,hZ,hZpot⟩ := ih (F.erase D) (erase_ssubset hDF)
        (hFd.mono (erase_subset _ _)) (fun E hE => hF E (mem_of_mem_erase hE))
        (O.erase H ∪ P) hOP (C ∪ D) hCUD hCDE hnewOC
      refine ⟨Z,hZ,?_⟩
      have hp := potential_union (arrangement_disjoint_finsets hX hOE hcross) Δ
      have he := potential_erase hHO Δ
      have hc := card_union_of_disjoint (hCF D hDF)
      have hs := sum_erase_add F (fun E : Finset V => (E.card : ℝ)) hDF
      have hc' : ((C ∪ D).card : ℝ) = (C.card : ℝ)+(D.card : ℝ) := by exact_mod_cast hc
      rw [hp,hc'] at hZpot
      nlinarith
    · obtain ⟨P,hP,hPO,hPF,hpot⟩ := shrink_shells hX hO hδ hΔ hΔ' hnext
      let W := C ∪ F.biUnion id
      have hWU : W ⊆ U := by
        intro u hu
        rcases mem_union.mp hu with hu | hu
        · exact hCU hu
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hF D hD).1 hu
      have hB : Arrangement X (W.image (fun u => ball u δ)) :=
        arrangement_balls (fun u hu => hUv u (hWU hu)) (hUd.mono hWU)
      have hcross : ∀H ∈ P, ∀K ∈ W.image (fun u => ball u δ),
          Disjoint (H.support X) (K.support X) := by
        intro H hH K hK
        obtain ⟨u,hu,rfl⟩ := mem_image.mp hK
        rcases mem_union.mp hu with hu | hu
        · obtain ⟨J,hJ,hsub⟩ := hPO H hH
          exact (hOC J hJ u hu).mono_left hsub
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hPF u (fun J hJ hh => hinter ⟨D,hD,u,hu,J,hJ,hh⟩) H hH).symm
      refine ⟨P ∪ W.image (fun u => ball u δ),arrangement_union hP hB hcross,?_⟩
      rw [potential_union (arrangement_disjoint_finsets hX hP hcross),
        potential_balls (show 6*Δ' ≤ δ by linarith)]
      have hCW : Disjoint C (F.biUnion id) := by
        rw [Finset.disjoint_left]
        intro u hu hv
        obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
        exact Finset.disjoint_left.mp (hCF D hD) hu hv
      have hflat : (F.biUnion id).card = ∑D ∈ F, D.card := card_biUnion hFd
      have hwcard : (W.card : ℝ) = (C.card : ℝ)+∑D ∈ F, (D.card : ℝ) := by
        dsimp [W]
        rw [card_union_of_disjoint hCW,hflat,Nat.cast_add,Nat.cast_sum]
      rw [hwcard]
      have hsum : 0 ≤ ∑D ∈ F, (D.card : ℝ) := sum_nonneg (fun D _ => Nat.cast_nonneg _)
      have hmass : δ/4*(∑D ∈ F, (D.card : ℝ)) ≤
          (∑D ∈ F, (D.card : ℝ))*(δ-6*Δ') := by nlinarith
      nlinarith

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V] {J : Type*} [Fintype J] [PseudoMetricSpace J] {X : V → J → ℝ}

lemma compact_arrangement (hX : ∀v, isProfile (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (U : ℕ → Finset V) (F : ℕ → Finset (Finset V))
    (hδ : ∀i < q, 0 < δ i) (hΔ : ∀i < q, 2*δ i ≤ Δ i)
    (hΔ0 : ∀i ≤ q, 0 ≤ Δ i) (hnext : ∀i < q, 6*Δ (i+1) ≤ δ i/2)
    (hUv : ∀i < q, ∀u ∈ U i, (ball u (δ i)).Valid X)
    (hUd : ∀i < q, (U i : Set V).Pairwise
      (fun u v => Disjoint ((ball u (δ i)).support X) ((ball v (δ i)).support X)))
    (hFd : ∀i < q, (F i : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀i < q, ∀D ∈ F i, D ⊆ U i ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ i) ∧ 36*Δ i ≤ (D.card : ℝ)*δ i) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range q, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ q) Z := by
  have hex : ∀j ≤ q, ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range j, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ j) Z := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨∅,arrangement_empty,by simp [potential]⟩
    | succ j ih =>
      intro hj
      have hjq : j < q := by omega
      obtain ⟨O,hO,hpot⟩ := ih (by omega)
      obtain ⟨Z,hZ,hZp⟩ := compact_phase hX (hδ j hjq) (hΔ j hjq)
        (hΔ0 (j+1) hj) (hnext j hjq) (U j) (hUv j hjq) (hUd j hjq)
        (F j) (hFd j hjq) (hF j hjq) O hO ∅ (empty_subset _) (by simp) (by simp)
      refine ⟨Z,hZ,?_⟩
      simp only [card_empty,Nat.cast_zero,zero_mul,add_zero] at hZp
      rw [sum_range_succ]
      linarith
  exact hex q le_rfl

structure CompactFamily (X : V → J → ℝ) (δ Δ : ℝ) where
  bags : Finset (Finset V)
  nonempty : bags.Nonempty
  radius_pos : 0 < δ
  bags_disjoint : (bags : Set (Finset V)).Pairwise Disjoint
  balls_disjoint : (bags.biUnion id : Set V).Pairwise
    (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))
  cardinal : ∀D ∈ bags, 2 ≤ D.card
  diameter : ∀D ∈ bags, ∀u ∈ D, ∀v ∈ D, normDistance (X u) (X v) ≤ Δ
  compact : ∀D ∈ bags, 36*Δ ≤ (D.card : ℝ)*δ

lemma CompactFamily.ball_valid (hX : ∀v, isProfile (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) {u : V} (hu : u ∈ F.bags.biUnion id) :
    (ball u δ).Valid X := by
  obtain ⟨D,hD,huD⟩ := mem_biUnion.mp hu
  have hcard := F.cardinal D hD
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  have hdist := disjoint_balls_distance hX u v (F.balls_disjoint hu hvU hvu.symm)
  refine ⟨le_rfl,F.radius_pos,fun _ => rfl,⟨u,by simp [ball,normDistance_self]⟩,v,?_⟩
  change δ ≤ normDistance (X v) (X u)
  rw [normDistance_comm]
  linarith [F.radius_pos]

lemma CompactFamily.scale (hX : ∀v, isProfile (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) : 2*δ ≤ Δ := by
  obtain ⟨D,hD⟩ := F.nonempty
  have hcard := F.cardinal D hD
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0 < D.card)
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have huU : u ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hu⟩
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  exact (disjoint_balls_distance hX u v (F.balls_disjoint huU hvU hvu.symm)).trans
    (F.diameter D hD u hu v hv)

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset RadialShell

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

lemma arrangement_length_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → J → ℝ) (hX : ∀v, isProfile (X v))
    {O : Finset (RadialShell (Fin n))} (hO : Arrangement X O) :
    (k:ℝ)*potential 0 O ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  classical
  obtain ⟨Y,hY⟩ := Classical.axiomOfChoice hX
  have hXY : X = fun v => profile (Y v) := funext hY
  subst X
  have hb := shell_length_bound G hk Y (fun H : O => Y H.val.center)
    (fun H : O => H.val.inner) (fun H : O => H.val.outer)
    (fun H => (hO.1 H.val H.property).2.1.le)
    (fun H => by
      simpa only [normDistance, profile_norm_sub] using
        (hO.1 H.val H.property).2.2.2.1)
    (fun H => by
      simpa only [normDistance, profile_norm_sub] using
        (hO.1 H.val H.property).2.2.2.2) ?_
  · convert hb using 2
    · rw [potential,Finset.sum_coe_sort O (fun H : RadialShell (Fin n) => H.outer-H.inner)]
      apply sum_congr rfl
      intro H hH
      simp only [capacity,mul_zero,sub_zero]
      exact max_eq_left (valid_width_pos (hO.1 H hH)).le
    · simp only [normDistance,profile_norm_sub]
  · intro H K hne
    apply Set.disjoint_left.mpr
    rintro w ⟨hw, hHa, hHb⟩ ⟨_, hKa, hKb⟩
    exact Set.disjoint_left.mp (hO.2 H.property K.property (Subtype.val_injective.ne hne))
      ⟨hw,hHb,Or.inr hHa⟩ ⟨hw,hKb,Or.inr hKa⟩

lemma metric_compact_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → J → ℝ) (hX : ∀v, isProfile (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (F : ∀i, CompactFamily X (δ i) (Δ i))
    (hnext : ∀i, i+1 < q → Δ (i+1) ≤ δ i/12) :
    (k:ℝ)/4*(∑i ∈ range q, δ i*(∑D ∈ (F i).bags, (D.card : ℝ))) ≤
      ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let D := fun i => if i < q then Δ i else 0
  have hD0 : ∀i ≤ q, 0 ≤ D i := by
    intro i hi
    dsimp [D]
    split_ifs with hh
    · linarith [(F i).scale hX,(F i).radius_pos]
    · exact le_rfl
  obtain ⟨Z,hZ,hZp⟩ := compact_arrangement hX q δ D
    (fun i => (F i).bags.biUnion id) (fun i => (F i).bags)
    (fun i _ => (F i).radius_pos)
    (fun i hi => by simpa [D,hi] using (F i).scale hX) hD0
    (by
      intro i hi
      dsimp [D]
      split_ifs with hh
      · linarith [hnext i hh]
      · linarith [(F i).radius_pos])
    (fun i _ u hu => (F i).ball_valid hX hu)
    (fun i _ => (F i).balls_disjoint)
    (fun i _ => (F i).bags_disjoint)
    (by
      intro i hi S hS
      refine ⟨?_,?_,?_,?_⟩
      · intro u hu; exact mem_biUnion.mpr ⟨S,hS,hu⟩
      · exact card_pos.mp (by have := (F i).cardinal S hS; omega)
      · simpa [D,hi] using (F i).diameter S hS
      · simpa [D,hi] using (F i).compact S hS)
  simp only [D,lt_self_iff_false,ite_false] at hZp
  have hmul := mul_le_mul_of_nonneg_left hZp (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hlength := arrangement_length_bound G hk X hX hZ
  nlinarith

lemma doubled_compact_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → J)
    (q : ℕ) (δ Δ : ℕ → ℝ)
    (F : ∀i, CompactFamily (fun v => profile (plus (X v))) (δ i) (Δ i))
    (hnext : ∀i, i+1 < q → Δ (i+1) ≤ δ i/12) :
    (k:ℝ)/4*(∑i ∈ range q, δ i*(∑D ∈ (F i).bags, (D.card : ℝ))) ≤
      ∑e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
  simpa only [normDistance, profile_norm_sub, dist_plus] using
    metric_compact_bound G hk (fun v => profile (plus (X v)))
      (fun v => ⟨plus (X v),rfl⟩) q δ Δ F hnext

end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
