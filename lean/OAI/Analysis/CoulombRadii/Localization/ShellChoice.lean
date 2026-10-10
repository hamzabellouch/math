import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CountUnits

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCountSecondMoment_cover {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {B : Set Space} (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c)) (hcover : B⊆⋃ c, A c) :
    localCountSecondMoment ψ B≤(Fintype.card C:ℝ)*∑ c, localCountSecondMoment ψ (A c) := by
  unfold localCountSecondMoment
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2),←integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact (integrable_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2)).const_mul _
  · filter_upwards [] with x
    rw [←Finset.sum_mul,←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (pow_le_pow_left₀ (localCount_nonneg B x) (localCount_cover A hcover x) 2).trans
      (by simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun c => localCount (A c) x))

lemma localCount_disjoint_sum_le {n : ℕ} {C : Type*} [Fintype C] {B : Set Space}
    (A : C → Set Space) (hsub : ∀ c, A c⊆B)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) (x : Configuration n) :
    (∑ c, localCount (A c) x)≤localCount B x := by
  unfold localCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : ∃ c, position x i∈A c
  · obtain ⟨c,hc⟩ := hx
    rw [indicator_of_mem (hsub c hc)]
    have he : ∑ d, (A d).indicator (fun _ => (1:ℝ)) (position x i)=1 := by
      rw [Finset.sum_eq_single c]
      · exact indicator_of_mem hc _
      · intro d hd hdc
        apply indicator_of_notMem
        intro hd'
        exact Set.disjoint_left.mp (hdis hdc) hd' hc
      · simp
    exact he.le
  · have hn (c : C) : position x i∉A c := fun hc => hx ⟨c,hc⟩
    simp only [indicator_of_notMem (hn _),Finset.sum_const_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma localCountSecondMoment_disjoint_sum_le {n : ℕ} {C : Type*} [Fintype C] (ψ : H1Vector n)
    {B : Set Space} (hB : MeasurableSet B) (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c))
    (hsub : ∀ c, A c⊆B) (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    (∑ c, localCountSecondMoment ψ (A c))≤localCountSecondMoment ψ B := by
  unfold localCountSecondMoment
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2)]
  apply integral_mono_ae (integrable_finsetSum _ (fun c _ => localCount_weight_integrable ψ (hA c) s 2))
    (localCount_weight_integrable ψ hB s 2)
  filter_upwards [] with x
  rw [←Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun c _ => localCount_nonneg (A c) x)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun c _ => localCount_nonneg (A c) x))
      (localCount_disjoint_sum_le A hsub hdis x) 2)

def deletedShell (y : Space) (t b : ℝ) : Set Space := {z | t-7*b≤‖z-y‖ ∧ ‖z-y‖≤t+b}

lemma deletedShell_measurable (y : Space) (t b : ℝ) : MeasurableSet (deletedShell y t b) := by
  change MeasurableSet ({z : Space | t-7*b≤‖z-y‖} ∩ {z : Space | ‖z-y‖≤t+b})
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet.inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet

lemma deletedShell_disjoint {y : Space} {t u b : ℝ} (h : t+8*b<u) :
    Disjoint (deletedShell y t b) (deletedShell y u b) := by
  apply Set.disjoint_left.mpr
  intro z hz ht
  have := hz.2
  have := ht.1
  linarith

theorem exists_deletedShell_small {n : ℕ} (ψ : H1Vector n) (y : Space)
    {a b : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) :
    ∃ t∈Set.Icc (5*a) (6*a), localCountSecondMoment ψ (deletedShell y t b)≤
      (18*b/a)*localCountSecondMoment ψ (Metric.closedBall y (7*a)) := by
  let N : ℕ := ⌊a/(9*b)⌋₊
  have hq : 2≤a/(9*b) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hfloor : (N:ℝ)≤a/(9*b) := Nat.floor_le (by positivity)
  have hlt : a/(9*b)<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have hNp : 0<N := by
    have : (1:ℝ)<(N:ℝ) := by linarith
    exact_mod_cast (lt_trans zero_lt_one this)
  have hN : a/(18*b)≤(N:ℝ) := by
    have hN1 : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hNp
    have he : a/(9*b)=2*(a/(18*b)) := by ring
    linarith
  let t : Fin N → ℝ := fun j => 5*a+9*b*(j.val:ℝ)
  have ht (j : Fin N) : t j∈Set.Icc (5*a) (6*a) := by
    have hj : (j.val:ℝ)≤(N:ℝ) := by exact_mod_cast (Nat.le_of_lt j.isLt)
    have hh : 9*b*(N:ℝ)≤a := by nlinarith [(le_div_iff₀ (by positivity : 0<9*b)).mp hfloor]
    dsimp [t]
    constructor
    · have hj0 : (0:ℝ)≤ j.val := Nat.cast_nonneg _
      nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hj (by positivity : 0≤9*b)]
  let A : Fin N → Set Space := fun j => deletedShell y (t j) b
  have hsub (j : Fin N) : A j⊆Metric.closedBall y (7*a) := by
    intro z hz
    change t j-7*b≤‖z-y‖ ∧ ‖z-y‖≤t j+b at hz
    rw [Metric.mem_closedBall,dist_eq_norm]
    linarith [(ht j).2]
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij|hji
    · apply deletedShell_disjoint (y:=y) (t:=t i) (u:=t j) (b:=b)
      have hv : (i.val:ℝ)+1≤ j.val := by exact_mod_cast (show i.val+1≤ j.val from hij)
      dsimp [t]
      nlinarith
    · have H : t j+8*b<t i := by
        have hv : (j.val:ℝ)+1≤ i.val := by exact_mod_cast (show j.val+1≤ i.val from hji)
        dsimp [t]
        nlinarith
      exact (deletedShell_disjoint (y:=y) H).symm
  have HS := localCountSecondMoment_disjoint_sum_le ψ measurableSet_closedBall A
    (fun j => deletedShell_measurable y (t j) b) hsub hdis
  have hsome : ∃ j : Fin N, localCountSecondMoment ψ (A j)≤
      localCountSecondMoment ψ (Metric.closedBall y (7*a))/(N:ℝ) := by
    by_contra hn
    push Not at hn
    have : Nonempty (Fin N) := ⟨⟨0,hNp⟩⟩
    have H := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty (fun j _ => hn j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    rw [mul_div_cancel₀ _ (show (N:ℝ)≠0 by exact_mod_cast (Nat.ne_of_gt hNp))] at H
    linarith
  obtain ⟨j,hj⟩ := hsome
  refine ⟨t j,ht j,hj.trans ?_⟩
  apply (div_le_iff₀ (by exact_mod_cast hNp : (0:ℝ)<N)).mpr
  have hprod : a≤18*b*(N:ℝ) := by
    have H := (div_le_iff₀ (by positivity : 0<18*b)).mp hN
    nlinarith
  have hr : 1≤18*b/a*(N:ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by simpa using hprod)
  nlinarith [mul_le_mul_of_nonneg_right hr (localCountSecondMoment_nonneg ψ (Metric.closedBall y (7*a)))]

end Coulomb
end

end
end

end OAI
