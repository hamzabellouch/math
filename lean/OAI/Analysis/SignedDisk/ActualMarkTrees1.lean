import OAI.Analysis.SignedDisk.FiniteLabels2

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

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

theorem direction_at_prefix {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {q : Grid N} {p s : List (Grid N)}
    (hp : activePath (tree (fun q => vectorMass h r q) k b q) (p++s)) :
    direction (1:ℂ) (vector (atPath (tree (fun q => vectorMass h r q) k b q) p)) =
      DirectionNeighbors.theta h (scale r (k-p.length)) (lastVertex q p) := by
  have hlen : p.length ≤ k := by have := active_length _ hp; simp only [List.length_append] at this; omega
  rw [atPath_tree _ b q p hlen,vector_actual hr hR hN hh hsupp]
  have hpa := active_append hp
  rw [atPath_tree _ b q p hlen] at hpa
  have hpos : 0 < b*pathWeight q p := lt_of_le_of_ne
    (mul_nonneg hb (pathWeight_nonneg q p)) (Ne.symm (active_ne_zero _ hpa))
  exact direction_smul_pos _ _ hpos

open DyadicHats IntrinsicMarks Finset DirectionNeighbors ActualLabels

def pathEnergy (h : ℂ → ℂ) (r : ℝ) (k : ℕ) {N : ℕ} (q : Grid N)
    (p : List (Grid N)) : ℝ := energy h (scale r (k-p.length)) (lastVertex q p)

def pathSwitches (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (x : ℂ)
    {N : ℕ} (p : List (Grid N)) (b : ℕ) : ℝ :=
  ∑ i ∈ Ico b (p.length+1), switchCost h (fun j => scale r (k-j)) x i

lemma mark_nonneg {ι : Type*} [Fintype ι] (t : Tree ι ℂ) (p : List ι) :
    0 ≤ rootMarkIndicator (1:ℂ) (1/800) t p := by
  rcases rootMarkIndicator_cases (1:ℂ) (1/800) t p with h | h
  · exact h.symm.le
  · exact h.symm ▸ zero_le_one

/-- The switch bound on every genuinely occupied path, using its complete
intrinsic history, even before the particle's birth. -/
theorem path_switch_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {p : List (Grid N)} (hp : activePath (tree (fun q => vectorMass h r q) k 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) {x : ℂ} (hx : hat r (lastVertex q p) x ≠ 0) :
    pathSwitches h r k x p b ≤ 2+
      2*pathCharge (rootMarkIndicator (1:ℂ) (1/800) (tree (fun q => vectorMass h r q) k 1 q)) p b+
      2000000*pathCharge (pathEnergy h r k q) p b := by
  classical
  let t := tree (fun q => vectorMass h r q) k 1 q
  let M := rootMarkIndicator (1:ℂ) (1/800) t
  let rs : ℕ → ℝ := fun i => scale r (k-i)
  let qs : ℕ → ℤ × ℤ := fun i => lastVertex q (p.take i)
  let E : ℕ → ℝ := fun i => energy h (rs i) (qs i)
  let A : ℕ → ℂ := fun i => rootAnchor (1:ℂ) (1/800) t (p.take i)
  let bad : ℕ → Bool := fun i => decide (M (p.take i) ≠ 0 ∨ (1/1000:ℝ)^2 < E i)
  have hlen : p.length = k := active_length _ hp
  have hpos (i : ℕ) : 0 < rs i := scale_pos hr _
  have he0 (i : ℕ) : 0 ≤ E i := energy_nonneg h _ _
  have hpref (i : ℕ) : activePath t (p.take i++p.drop i) := by
    simpa only [List.take_append_drop] using hp
  have hloc (i : ℕ) (hi : i ≤ p.length) : boxNorm (x-point (rs i) (qs i)) ≤ 50*rs i := by
    have hl := active_prefix_locality (fun q => vectorMass h r q) hr (hpref i)
      (by simpa only [List.take_append_drop] using hx)
    have hli : (p.take i).length = i := by simp only [List.length_take,min_eq_left hi]
    simp only [hli] at hl
    exact hl.le.trans (by dsimp only [rs,qs]; nlinarith [scale_pos hr (k-i)])
  have hdir (i : ℕ) (hi : i ≤ p.length) :
      direction (1:ℂ) (vector (atPath t (p.take i))) = theta h (rs i) (qs i) := by
    have hd := direction_at_prefix hr hR hN hh hsupp (by norm_num : (0:ℝ) ≤ 1) (hpref i)
    simpa only [List.length_take,min_eq_left hi] using hd
  have hbad (i : ℕ) : bad i = false → M (p.take i) = 0 ∧ E i ≤ (1/1000:ℝ)^2 := by
    simp only [bad,decide_eq_false_iff_not,not_or,not_not,not_lt]
    exact id
  have hs := switchCost_sum h rs qs x A bad (by omega : b ≤ k)
    (fun i _ => hpos (i+1))
    (fun i hi => hloc (i+1) (by simp only [Finset.mem_Ico] at hi; omega))
    (fun i _ hi => (hbad (i+1) hi).2)
    (fun i hi he => by
      have hil : i < p.length := by simp only [Finset.mem_Ico] at hi; omega
      have ha := rootAnchor_step (1:ℂ) (by norm_num : (0:ℝ) ≤ 1/800) t p
        (activePath_valid hp) hil (hbad (i+1) he).1
      rw [hdir (i+1) (by omega)] at ha
      exact ha)
  have hind (i : ℕ) : (if bad i then (1:ℝ) else 0) ≤ M (p.take i)+1000000*E i := by
    rcases rootMarkIndicator_cases (1:ℂ) (1/800) t (p.take i) with hm | hm
    · change M (p.take i) = 0 at hm
      by_cases he : (1/1000:ℝ)^2 < E i
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_true,ite_true]
        nlinarith
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_false,Bool.false_eq_true,ite_false]
        nlinarith [he0 i]
    · change M (p.take i) = 1 at hm
      have hh0 := he0 i
      by_cases he : bad i = true <;> simp [he,show M (p.take i) = 1 from hm] <;> nlinarith
  have hterm : (∑ i ∈ Ico b k, if bad (i+1) then (1:ℝ) else 0) ≤
      pathCharge M p b+1000000*pathCharge (pathEnergy h r k q) p b := by
    calc
      _ ≤ ∑ i ∈ Ico b k, (M (p.take (i+1))+1000000*E (i+1)) :=
        sum_le_sum (fun i _ => hind (i+1))
      _ = ∑ i ∈ Ico (b+1) (k+1), (M (p.take i)+1000000*E i) := by
        exact sum_Ico_add' (fun i => M (p.take i)+1000000*E i) b k 1
      _ ≤ ∑ i ∈ Ico b (p.length+1), (M (p.take i)+1000000*E i) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_Ico] at hi ⊢
          omega
        · intro i _ _
          exact add_nonneg (mark_nonneg t _) (mul_nonneg (by norm_num) (he0 i))
      _ = _ := by
        rw [pathCharge_sum,pathCharge_sum,sum_add_distrib,mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        congr 1
        have hil : i ≤ p.length := by have := (Finset.mem_Ico.mp hi).2; omega
        simp only [E,rs,qs,pathEnergy,List.length_take,min_eq_left hil]
  have hsum : pathSwitches h r k x p b = switchCost h rs x b+
      ∑ i ∈ Ico b k, switchCost h rs x (i+1) := by
    change (∑ i ∈ Ico b (p.length+1), switchCost h rs x i) = _
    rw [hlen,Finset.sum_eq_sum_Ico_succ_bot (by omega : b < k+1),Finset.sum_Ico_add']
  rw [hsum]
  have h1 := switchCost_le_one h rs x b
  change _ ≤ 2+2*pathCharge M p b+2000000*pathCharge (pathEnergy h r k q) p b
  linarith

end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

def sign (b : Bool) : ℝ := if b then 1 else -1
lemma sign_cases (b : Bool) : sign b = 1 ∨ sign b = -1 := by cases b <;> simp [sign]
lemma sign_sq (b : Bool) : sign b^2 = 1 := by cases b <;> norm_num [sign]

def cellPrice (N : ℕ) (r : ℝ) (h : ℂ → ℂ) (k : ℕ) (S : Finset (Grid N)) : ℝ :=
  ∑ q ∈ S, rootPrice N r h k q

def rootWeight {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) : ℝ :=
  ∑ q ∈ S, coeff N (k-j) q s
lemma rootWeight_nonneg {N : ℕ} (S : Finset (Grid N)) (k j : ℕ) (s : Grid N) :
    0 ≤ rootWeight S k j s := sum_nonneg (fun q _ => coeff_nonneg N (k-j) q s)

abbrev ErrorIndex (N k : ℕ) := Fin (k+1) × Grid N × Bool

def smallPiece {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (i : ErrorIndex N k) : ErrorPiece 2 :=
  (errorPiece hh hr k i.1 (Nat.le_of_lt_succ i.1.isLt) p i.2.1 n (sign i.2.2)).weight
    (rootWeight S k i.1 i.2.1)

lemma smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).mass ≤ (scale r k)⁻¹*2*
      (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1) := by
  rw [smallPiece,ErrorPiece.mass_weight _ (rootWeight_nonneg ..)]
  calc
    _ ≤ rootWeight S k i.1 i.2.1*((scale r k)⁻¹*
        (2*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (errorPiece_mass hr hR hN hh hsupp k i.1
        (Nat.le_of_lt_succ i.1.isLt) p i.2.1 hn (sign_sq _)) (rootWeight_nonneg ..)
    _ = _ := by ring

lemma discounted_smallPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) (i : ErrorIndex N k) :
    (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass ≤
      (scale r k)⁻¹*2*(rho^(k-i.1)*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) := by
  have hs : (smallPiece hh hr k p S n i).size^(1/100:ℝ) = rho^(k-i.1) :=
    scale_discount hr (Nat.le_of_lt_succ i.1.isLt)
  rw [hs]
  calc
    _ ≤ rho^(k-i.1)*((scale r k)⁻¹*2*
        (rootWeight S k i.1 i.2.1*densityDefect N r (fun x => coordinate n (sign i.2.2) (h x)) i.1 i.2.1)) :=
      mul_le_mul_of_nonneg_left (smallPiece_mass hr hR hN hh hsupp k p S hn i) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

lemma weighted_defect_sum {N : ℕ} (r : ℝ) (h : ℂ → ℝ) (k : ℕ) (S : Finset (Grid N)) :
    (∑ j : Fin (k+1), ∑ s : Grid N, rho^(k-j.val)*(rootWeight S k j s*densityDefect N r h j s)) =
      ∑ q ∈ S, scalarPrice N r h rho k q := by
  simp only [rootWeight,sum_mul,mul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  unfold scalarPrice
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  rw [mul_sum]

lemma smallPiece_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*
      ∑ q ∈ S, (scalarPrice N r (fun x => coordinate n 1 (h x)) rho k q+
        scalarPrice N r (fun x => coordinate n (-1) (h x)) rho k q) := by
  apply (sum_le_sum (fun i _ => discounted_smallPiece_mass hr hR hN hh hsupp k p S hn i)).trans_eq
  rw [← mul_sum]
  congr 1
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,sign,Bool.false_eq_true,
    ite_false,ite_true,sum_add_distrib]
  rw [weighted_defect_sum,weighted_defect_sum,← sum_add_distrib]

lemma smallPiece_common_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (smallPiece hh hr k p S n) (1/100) ≤ (scale r k)⁻¹*2*cellPrice N r h k S := by
  apply (smallPiece_price hr hR hN hh hsupp k p S (fixedPalette.unit n hn)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (scale_pos hr k).le) (by norm_num))
  apply sum_le_sum
  intro q _
  apply single_le_sum _ hn
  intro n _
  exact add_nonneg
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)
    (scalarPrice_nonneg hr hR hN (scalar_integrable hh _) (scalar_support hsupp _) k q)

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

def goodRoots {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Finset (Grid N) :=
  by classical exact S.filter (fun q => Good n (DirectionNeighbors.theta h (scale r k) q))
def badRoots {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Finset (Grid N) :=
  by classical exact S.filter (fun q => ¬Good n (DirectionNeighbors.theta h (scale r k) q))

def rootSum {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) (y : ℂ) : ℂ :=
  ∑ q ∈ S, rootVector N r h k q n y

lemma rootSum_integrable {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h)
    (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : Integrable (rootSum h r k S n) :=
  integrable_finsetSum S (fun _ _ => rootVector_integrable hh r k _ n)

lemma rootSum_partition {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) (y : ℂ) :
    rootSum h r k (goodRoots h r k S n) n y+rootSum h r k (badRoots h r k S n) n y = rootSum h r k S n y := by
  classical
  exact sum_filter_add_sum_filter_not S (fun q => Good n (DirectionNeighbors.theta h (scale r k) q)) _

lemma rootSum_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (∫ y, ‖rootSum h r k S n y‖) ≤ 4*∑ q ∈ S, scalarMass h (scale r k) q := by
  calc
    _ ≤ ∫ y, ∑ q ∈ S, ‖rootVector N r h k q n y‖ :=
      integral_mono (rootSum_integrable hh r k S n).norm
        (integrable_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm))
        (fun y => norm_sum_le _ _)
    _ = ∑ q ∈ S, ∫ y, ‖rootVector N r h k q n y‖ :=
      integral_finsetSum S (fun _ _ => (rootVector_integrable hh r k _ n).norm)
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum (fun q _ => rootVector_mass hr hR hN hh hsupp k q hn)

/-- The actual normalized positive-cone part on one cell. -/
def goodCone {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) : ConeDensity (axis n s) (1/2) where
  density := rescale p (scale r k) (rootSum h r k (goodRoots h r k S n) n)
  integrable := integrable_rescale (rootSum_integrable hh r k _ n) p (scale_pos hr k).ne'
  cone := by
    classical
    apply ae_of_all
    intro X
    have hc := cone_sum (by norm_num : (0:ℝ) ≤ 1/2) (goodRoots h r k S n)
      (fun q => rootVector N r h k q n (p+scale r k • X)) (by
        intro q hq
        have hg : Good n (DirectionNeighbors.theta h (scale r k) q) := (mem_filter.mp hq).2
        exact rootVector_cone hr hR hN hh hsupp k q hn hg hs _)
    simp only [rescale,norm_smul,Real.norm_eq_abs,abs_of_pos (scale_pos hr k),real_inner_smul_right]
    change (1/2:ℝ)*(scale r k*‖rootSum h r k (goodRoots h r k S n) n (p+scale r k • X)‖) ≤ _
    dsimp only [rootSum]
    nlinarith [mul_le_mul_of_nonneg_left hc (scale_pos hr k).le]

def badPrice {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) (n : ℂ) : ℝ :=
  ∑ q ∈ badRoots h r k S n, scalarMass h (scale r k) q

/-- Bad cone roots are exactly the unrestricted size-one part. -/
def badPiece {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : ErrorPiece 2 :=
  unitPiece (rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n))
    (integrable_rescale (rootSum_integrable hh r k _ n) p (scale_pos hr k).ne') 2

lemma badPiece_mass {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) :
    (badPiece hr hh k p S n).mass ≤ (scale r k)⁻¹*4*badPrice h r k S n := by
  change (∫ X, ‖rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X‖) ≤ _
  rw [mass_rescale _ _ (scale_pos hr k)]
  simpa only [mul_assoc,badPrice] using mul_le_mul_of_nonneg_left
    (rootSum_mass hr hR hN hh hsupp k (badRoots h r k S n) hn) (inv_nonneg.mpr (scale_pos hr k).le)

def cellErrors {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : Option (ErrorIndex N k) → ErrorPiece 2
  | none => badPiece hr hh k p S n
  | some i => smallPiece hh hr k p S n i

lemma cellErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (cellErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*badPrice h r k S n+2*cellPrice N r h k S) := by
  simp only [errorPrice,Fintype.sum_option,cellErrors,show (badPiece hr hh k p S n).size = 1 from rfl,
    Real.one_rpow,one_mul]
  have h1 := badPiece_mass hr hR hN hh hsupp k p S (fixedPalette.unit n hn)
  have h2 := smallPiece_common_price hr hR hN hh hsupp k p S hn
  unfold errorPrice at h2
  linarith

open DyadicHats ConeCoordinates ConeScalar Finset PricePieces LocalCancellation AffineDensities

lemma smallPiece_pair_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (j : Fin (k+1)) (q : Grid N) (X : ℂ) :
    (∑ b : Bool, (smallPiece hh hr k p S n (j,q,b)).density X) =
      rootWeight S k j q • rescale p (scale r k) (errorVector N r h j q n) X := by
  simp only [Fintype.sum_bool,smallPiece,ErrorPiece.weight,errorPiece,sign,
    Bool.false_eq_true,ite_false,ite_true,rescale,errorVector]
  module

lemma smallPiece_sum {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) (X : ℂ) :
    (∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) =
      rescale p (scale r k) (fun y => ∑ q ∈ S, ∑ j ∈ range (k+1),
        ∑ s : Grid N, coeff N (k-j) q s • errorVector N r h j s n y) X := by
  simp only [Fintype.sum_prod_type,smallPiece_pair_sum,rootWeight,sum_smul,rescale,smul_sum]
  simp_rw [Finset.sum_comm (s := univ) (t := S)]
  apply sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro s _
  module

/-- Exact cell decomposition before imposing the local partition-of-unity
region. Both its scalar coordinates and all error densities are the actual
finite dyadic construction. -/
theorem cell_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : ‖n‖ = 1) {s : ℝ} (hs : s = 1 ∨ s = -1) (X : ℂ) :
    (goodCone hr hR hN hh hsupp k p S hn hs).density X+
      (∑ i, (cellErrors hr hh k p S n i).density X) =
      rescale p (scale r k) (fun y => (∑ q ∈ S, hat (scale r k) q y) • h y) X := by
  rw [Fintype.sum_option]
  change rescale p (scale r k) (rootSum h r k (goodRoots h r k S n) n) X+
    (rescale p (scale r k) (rootSum h r k (badRoots h r k S n) n) X+
      ∑ i : ErrorIndex N k, (smallPiece hh hr k p S n i).density X) = _
  rw [smallPiece_sum]
  simp only [rescale,← smul_add,← add_assoc,rootSum_partition]
  rw [sum_smul]
  congr 1
  simp only [rootSum,← sum_add_distrib]
  exact sum_congr rfl (fun q _ => (vector_decomposition hr hR hN hsupp k q hn _).symm)

end CommonPrices

namespace DirectionNeighbors
open DyadicHats
lemma mem_window_comm (d : ℕ) (p q : ℤ × ℤ) : p ∈ window d q ↔ q ∈ window d p := by
  rw [mem_window_iff (by norm_num : (0:ℝ) < 1),mem_window_iff (by norm_num : (0:ℝ) < 1),boxNorm_sub_comm]

lemma card_window (d : ℕ) (q : ℤ × ℤ) : (window d q).card = (2*d+1)^2 := by
  change ((Finset.Icc (q.1-(d:ℤ)) (q.1+d)) ×ˢ
    (Finset.Icc (q.2-(d:ℤ)) (q.2+d))).card = _
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have hq (z : ℤ) : (z+(d:ℤ)+1-(z-d)).toNat = 2*d+1 := by omega
  rw [hq,hq,pow_two]

end DirectionNeighbors

end SignedDisk

end

end OAI
