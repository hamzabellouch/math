import OAI.Geometry.Kahler.BasePacking

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma separated_local_count {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    ((P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)).card : ℝ) ≤ 9*(u+1/3)^2 := by
  classical
  let S := P.filter (fun p => projectiveDistance ξ p < u/Real.sqrt k)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs : 1 ≤ Real.sqrt (k:ℝ) := (Real.one_le_sqrt).mpr (by exact_mod_cast hk)
  have hs0 : 0 < Real.sqrt (k:ℝ) := lt_of_lt_of_le zero_lt_one hs
  let r := 1/(3*Real.sqrt (k:ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_one (by positivity)).mpr; linarith
  have hsep : ProjectivelySeparated (2*r) S := by
    intro p hp q hq hpq
    have ht := hP p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
    have he : 2*r ≤ D/Real.sqrt (k:ℝ) := by dsimp [r]; field_simp; nlinarith
    exact he.trans ht
  have hd := separated_caps_disjoint hsep
  have he : 2*r/2 = r := by ring
  rw [he] at hd
  have hm : sigma.real (⋃ p ∈ S, projectiveCap p r) = (S.card:ℝ)*r^2 := by
    rw [measureReal_biUnion_finset hd (fun p _ => projectiveCap_measurable p r)]
    simp only [projectiveCap_real _ hr.le hr1,Finset.sum_const,nsmul_eq_mul]
  have hsmall : (⋃ p ∈ S, projectiveCap p r) ⊆ projectiveCap ξ ((u+1/3)/Real.sqrt (k:ℝ)) := by
    intro η hη
    obtain ⟨p,hp,hηp⟩ := mem_iUnion₂.mp hη
    have hp' := (Finset.mem_filter.mp hp).2
    change projectiveDistance η p < r at hηp
    change projectiveDistance η ξ < _
    have ht := projectiveDistance_triangle η p ξ
    rw [projectiveDistance_symm p ξ] at ht
    dsimp [r] at hηp
    have he : u/Real.sqrt (k:ℝ)+1/(3*Real.sqrt (k:ℝ)) = (u+1/3)/Real.sqrt (k:ℝ) := by field_simp
    linarith
  have hb : (S.card:ℝ)*r^2 ≤ ((u+1/3)/Real.sqrt (k:ℝ))^2 := by
    by_cases hh : (u+1/3)/Real.sqrt (k:ℝ) ≤ 1
    · rw [← hm]
      simpa only [projectiveCap_real _ (by positivity : 0 ≤ (u+1/3)/Real.sqrt (k:ℝ)) hh] using measureReal_mono (μ := sigma) hsmall
    · have hv := measureReal_mono (μ := sigma) (subset_univ (⋃ p ∈ S, projectiveCap p r))
      rw [hm] at hv
      have hv1 : sigma.real univ = 1 := by simp [measureReal_def]
      rw [hv1] at hv
      have hh' : 1 < (u+1/3)/Real.sqrt (k:ℝ) := lt_of_not_ge hh
      nlinarith
  change (S.card:ℝ) ≤ _
  dsimp [r] at hb
  have hsq := Real.sq_sqrt hk0.le
  field_simp at hb
  nlinarith

lemma peak_exponential_bound (ξ p : Sphere) (k : ℕ) :
    ‖bracket (ξ:Base) (p:Base)‖^k ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2) := by
  have hd := projectiveDistance_sq ξ p
  have he := Real.one_sub_le_exp_neg (projectiveDistance ξ p^2)
  have hp := pow_le_pow_left₀ (sq_nonneg ‖bracket (ξ:Base) (p:Base)‖) (show ‖bracket (ξ:Base) (p:Base)‖^2 ≤ Real.exp (-projectiveDistance ξ p^2) by linarith) k
  rw [← Real.exp_nat_mul] at hp
  have he' : Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 = Real.exp ((k:ℝ)*(-projectiveDistance ξ p^2)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hp' : (‖bracket (ξ:Base) (p:Base)‖^k)^2 ≤ Real.exp (-(k:ℝ)*projectiveDistance ξ p^2/2)^2 := by simpa only [he',← pow_mul,mul_comm k 2] using hp
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hp'

lemma gaussian_sequence_summable : Summable (fun n : ℕ => 9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4)) := by
  have he : ‖Real.exp (-1:ℝ)‖ < 1 := by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num)
  have h0 := summable_geometric_of_norm_lt_one he
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 he
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 he
  have hsum : Summable (fun n : ℕ => 9*Real.exp 1*((n:ℝ)+2)^2*Real.exp (-(n:ℝ))) := by
    apply Summable.congr (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left (9*Real.exp 1))
    intro n
    rw [← Real.exp_nat_mul]
    simp only [mul_neg,mul_one]
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hn : -(n:ℝ)^2/4 ≤ 1-(n:ℝ) := by nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hp := Real.exp_le_exp.mpr hn
  rw [Real.exp_sub] at hp
  have heq : Real.exp 1/Real.exp (n:ℝ) = Real.exp 1*Real.exp (-(n:ℝ)) := by rw [Real.exp_neg,div_eq_mul_inv]
  rw [heq] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 9*((n:ℝ)+2)^2 by positivity)
  nlinarith

def gaussianConstant : ℝ := ∑' n : ℕ, 9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4)

lemma gaussianConstant_pos : 0 < gaussianConstant := by
  have h := gaussian_sequence_summable.le_tsum 0 (fun n hn => by positivity)
  norm_num at h
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 36) h

lemma gaussian_full_sum {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    (∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) ≤ gaussianConstant := by
  classical
  let t : Sphere → ℝ := fun p => Real.sqrt k*projectiveDistance ξ p
  let f : Sphere → ℕ := fun p => ⌊t p⌋₊
  let N := P.sup f+1
  have hmap : ∀ p ∈ P, f p ∈ Finset.range N := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hp))
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => Real.exp (-(t p)^2/4))]
  have hs0 : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have hbin : ∀ n : ℕ, (∑ p ∈ P with f p = n, Real.exp (-(t p)^2/4)) ≤
      9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4) := by
    intro n
    have hsub : P.filter (fun p => f p=n) ⊆ P.filter (fun p => projectiveDistance ξ p < ((n:ℝ)+1)/Real.sqrt k) := by
      intro p hp
      obtain ⟨hpP,hpn⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpP,?_⟩
      apply (lt_div_iff₀ hs0).mpr
      have hn := Nat.lt_floor_add_one (t p)
      change t p < (f p:ℝ)+1 at hn
      rw [hpn] at hn
      simpa only [t,mul_comm] using hn
    have hc := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    have hcount := separated_local_count hD hk hP ξ (show 0 ≤ (n:ℝ)+1 by positivity)
    have hcount' : ((P.filter (fun p => f p=n)).card:ℝ) ≤ 9*((n:ℝ)+2)^2 := by
      have hc' := hc.trans hcount
      nlinarith [show (0:ℝ) ≤ n by positivity]
    calc
      _ ≤ ∑ p ∈ P with f p=n, Real.exp (-(n:ℝ)^2/4) := by
        apply Finset.sum_le_sum
        intro p hp
        have hn := Nat.floor_le (show 0 ≤ t p from mul_nonneg hs0.le (projectiveDistance_nonneg ξ p))
        change (f p:ℝ) ≤ t p at hn
        rw [(Finset.mem_filter.mp hp).2] at hn
        apply Real.exp_le_exp.mpr
        nlinarith [show (0:ℝ) ≤ n by positivity]
      _ = ((P.filter (fun p => f p=n)).card:ℝ)*Real.exp (-(n:ℝ)^2/4) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount' (Real.exp_pos _).le
  exact (Finset.sum_le_sum (fun n _ => hbin n)).trans
    (gaussian_sequence_summable.sum_le_tsum _ (fun n hn => by positivity))

lemma peak_gaussian {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (ξ : Sphere) {u : ℝ} (hu : 0 ≤ u) :
    (∑ p ∈ P with u ≤ Real.sqrt k*projectiveDistance ξ p, ‖bracket (ξ:Base) (p:Base)‖^k)
      ≤ gaussianConstant*Real.exp (-u^2/4) := by
  classical
  have hk0 : (0:ℝ) ≤ k := by positivity
  have hs := Real.sq_sqrt hk0
  let S := P.filter (fun p => u ≤ Real.sqrt k*projectiveDistance ξ p)
  have hp : ∀ p ∈ S, ‖bracket (ξ:Base) (p:Base)‖^k ≤
      Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := by
    intro p hp
    apply (peak_exponential_bound ξ p k).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := (Finset.mem_filter.mp hp).2
    have hz : 0 ≤ Real.sqrt k*projectiveDistance ξ p := mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
    have he : (Real.sqrt k*projectiveDistance ξ p)^2 = (k:ℝ)*projectiveDistance ξ p^2 := by rw [mul_pow,hs]
    nlinarith
  calc
    _ ≤ ∑ p ∈ S, Real.exp (-u^2/4)*Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4) := Finset.sum_le_sum hp
    _ = Real.exp (-u^2/4)*(∑ p ∈ S, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-u^2/4)*(∑ p ∈ P, Real.exp (-(Real.sqrt k*projectiveDistance ξ p)^2/4)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp hn => (Real.exp_pos _).le)
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (gaussian_full_sum hD hk hP ξ) (Real.exp_pos (-u^2/4)).le

lemma peak_sphere_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) (ξ : Sphere) :
    ‖peakPolynomial P k (ξ:Base)‖ ≤ gaussianConstant := by
  classical
  have h := peak_gaussian hD hk hP ξ (u := 0) le_rfl
  have hn : ∀ p : Sphere, 0 ≤ Real.sqrt k*projectiveDistance ξ p := fun p => mul_nonneg (Real.sqrt_nonneg _) (projectiveDistance_nonneg _ _)
  simp only [hn,Finset.filter_true,zero_pow (by norm_num : (2:ℕ) ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one] at h
  apply (norm_sum_le _ _).trans
  simpa only [norm_pow] using h

end PinchedHartogs.BaseConstruction

end

end OAI
