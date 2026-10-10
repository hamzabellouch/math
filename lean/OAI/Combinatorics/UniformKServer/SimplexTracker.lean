import Mathlib

namespace OAI

namespace UniformKServer.SimplexTracker
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def simplex (a : ι → ℝ) : Prop := (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

def movement (a b : ι → ℝ) : ℝ := ∑ i, |a i-b i|

def transfer (a : ι → ℝ) (i j : ι) (s : ℝ) : ι → ℝ :=
  Function.update (Function.update a i (a i-s)) j (a j+s)

def objective (g : ι → ℝ → ℝ) (S : ℝ) (a₀ a : ι → ℝ) : ℝ :=
  (∑ i, g i (a i))+S*movement a a₀

structure AnalyticData (g : ι → ℝ → ℝ) (B h : ι → ℝ)
    (F : ι → ℝ → ℝ) (ell ct C A E : ℝ) : Prop where
  B_nonneg : ∀ i, 0 ≤ B i
  h_pos : ∀ i, 0 < h i
  ell_pos : 0 < ell
  ct_pos : 0 < ct
  A_nonneg : 0 ≤ A
  E_nonneg : 0 ≤ E
  eta_le : ∀ i, ct*h i/ell ≤ E
  multiplier : 2*A*(1+E) < C*ct
  F_pos : ∀ i x, 0 < x → x ≤ 1 → 0 < F i x
  denominator_bound : ∀ a, simplex a →
    (∑ i, a i*F i (a i)) ≤ A*(∑ i, a i*h i)
  continuous : ∀ i, ContinuousOn (g i) (Icc 0 1)
  derivative : ∀ i x, 0 < x → x ≤ 1 →
    HasDerivAt (g i) ((C*ell/F i x)*((∑ r, B r)-(1+ct*h i/ell)*B i/x)) x
  inward : ∀ i, 0 < B i →
    Tendsto (fun s : ℝ => (g i s-g i 0)/s) (𝓝[>] 0) atBot

omit [DecidableEq ι] in
theorem coordinate_le_one {a : ι → ℝ} (ha : simplex a) (i : ι) : a i ≤ 1 := by
  rw [← ha.2]
  exact Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem simplex_compact : IsCompact {a : ι → ℝ | simplex a} := by
  have h₁ : IsClosed {a : ι → ℝ | ∀ i, 0 ≤ a i} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {a : ι → ℝ | ∑ i, a i = 1} := isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1))).of_isClosed_subset (h₁.inter h₂)
  intro a ha
  exact ⟨ha.1, coordinate_le_one ha⟩

theorem sum_update (a : ι → ℝ) (i : ι) (t : ℝ) :
    ∑ j, Function.update a i t j = (∑ j, a j)+t-a i := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]; ring

theorem potential_update (g : ι → ℝ → ℝ) (a : ι → ℝ) (i : ι) (t : ℝ) :
    (∑ j, g j (Function.update a i t j)) = (∑ j, g j (a j))+g i t-g i (a i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => g j (a j)) (Finset.mem_univ i)]
  have he : ∑ j ∈ Finset.univ.erase i, g j (Function.update a i t j) =
      ∑ j ∈ Finset.univ.erase i, g j (a j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he, Function.update_self]; ring

theorem transfer_simplex {a : ι → ℝ} (ha : simplex a) {i j : ι} (hij : i ≠ j)
    {s : ℝ} (hs : 0 ≤ s) (hsi : s ≤ a i) : simplex (transfer a i j s) := by
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hrj : r = j
    · subst r; simp only [transfer, Function.update_self]; exact add_nonneg (ha.1 j) hs
    · by_cases hri : r = i
      · subst r; simp [transfer, Function.update_of_ne hij, sub_nonneg.mpr hsi]
      · simp [transfer, Function.update_of_ne hrj, Function.update_of_ne hri, ha.1 r]
  · simp only [transfer, sum_update, Function.update_of_ne hij.symm, ha.2]
    ring

theorem transfer_potential (g : ι → ℝ → ℝ) (a : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    (∑ r, g r (transfer a i j s r)) = (∑ r, g r (a r)) +
      (g i (a i-s)-g i (a i))+(g j (a j+s)-g j (a j)) := by
  simp only [transfer, potential_update, Function.update_of_ne hij.symm]
  ring

theorem transfer_movement (a b : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    movement (transfer a i j s) b ≤ movement a b+2*|s| := by
  unfold movement
  rw [transfer_potential (fun r t => |t-b r|) a hij]
  have hi := abs_add_le (a i-b i) (-s)
  simp only [abs_neg, ← sub_eq_add_neg] at hi
  have hj := abs_add_le (a j-b j) s
  have ei : a i-s-b i = a i-b i-s := by ring
  have ej : a j+s-b j = a j-b j+s := by ring
  rw [ei, ej]; linarith

theorem scalar_deficit {a eta E : ℝ} (ha : 0 ≤ a) (he : 0 ≤ eta) (hE : eta ≤ E) :
    a/(1+eta) ≤ a-a*eta/(1+E) := by
  have h₁ : 0 < 1+eta := by linarith
  have h₂ : 0 < 1+E := by linarith
  apply (div_le_iff₀ h₁).mpr
  apply (mul_le_mul_iff_right₀ h₂).mp
  have eqn : (a-a*eta/(1+E))*(1+eta)*(1+E) = a*(1+E)+a*eta*(E-eta) := by
    field_simp; ring
  nlinarith [mul_nonneg (mul_nonneg ha he) (sub_nonneg.mpr hE)]

omit [DecidableEq ι] in
theorem multiplier_pos {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E) : 0 < C := by
  have hn : 0 ≤ 2*A*(1+E) := mul_nonneg (mul_nonneg (by norm_num) H.A_nonneg) (by linarith [H.E_nonneg])
  have hp : 0 < C*ct := lt_of_le_of_lt hn H.multiplier
  exact pos_of_mul_pos_left hp H.ct_pos.le

omit [DecidableEq ι] in
theorem weighted_deficit {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a : ι → ℝ} (ha : simplex a) :
    (∑ i, a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell))) < 1 := by
  have hC := multiplier_pos H
  have hK : 0 < C*ell := mul_pos hC H.ell_pos
  have he : 0 < 1+E := by linarith [H.E_nonneg]
  have hT : 0 < ∑ i, a i*h i := by
    obtain ⟨i, hi, hai⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => ha.1 i)).mp
      (show 0 < ∑ i, a i from by rw [ha.2]; norm_num)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (ha.1 i) (H.h_pos i).le)
      ⟨i, hi, mul_pos hai (H.h_pos i)⟩
  have hs : ∀ i, a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)) ≤
      a i-(ct/(ell*(1+E)))*(a i*h i)+(2/(C*ell))*(a i*F i (a i)) := by
    intro i
    have hη : 0 ≤ ct*h i/ell := le_of_lt (div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos)
    have hp : 0 ≤ a i*F i (a i) := by
      rcases (ha.1 i).eq_or_lt with hz | hz
      · rw [← hz, zero_mul]
      · exact mul_nonneg hz.le (H.F_pos i _ hz (coordinate_le_one ha i)).le
    have hdef := scalar_deficit (ha.1 i) hη (H.eta_le i)
    have hself := div_le_self hp (show (1:ℝ) ≤ 1+ct*h i/ell by linarith)
    have hextra := mul_le_mul_of_nonneg_left hself (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hK.le)
    have eq₁ : a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)) =
        a i/(1+ct*h i/ell)+(2/(C*ell))*(a i*F i (a i)/(1+ct*h i/ell)) := by ring
    have eq₂ : a i*(ct*h i/ell)/(1+E) = (ct/(ell*(1+E)))*(a i*h i) := by field_simp
    rw [eq₁]
    rw [eq₂] at hdef
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ha.2] at hsum
  have hbound := mul_le_mul_of_nonneg_left (H.denominator_bound a ha) (show 0 ≤ 2/(C*ell) by positivity)
  have hco : 2*A/(C*ell) < ct/(ell*(1+E)) := by
    apply (div_lt_div_iff₀ hK (mul_pos H.ell_pos he)).mpr
    have hh := mul_lt_mul_of_pos_right H.multiplier H.ell_pos
    nlinarith
  have hf := mul_lt_mul_of_pos_right hco hT
  have heq : 2/(C*ell)*(A*(∑ i, a i*h i)) = 2*A/(C*ell)*(∑ i, a i*h i) := by ring
  rw [heq] at hbound
  linarith

omit [DecidableEq ι] in
theorem low_coordinate {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a : ι → ℝ} (ha : simplex a) (hS : 0 < ∑ i, B i) :
    ∃ i, (a i = 0 ∧ 0 < B i) ∨
      (0 < a i ∧ (C*ell/F i (a i))*((∑ r, B r)-(1+ct*h i/ell)*B i/a i) < -2*(∑ r, B r)) := by
  by_contra hn
  push Not at hn
  have hK : 0 < C*ell := mul_pos (multiplier_pos H) H.ell_pos
  have hpoint : ∀ i, B i ≤ (∑ r, B r)*(a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell))) := by
    intro i
    have heta : 0 < 1+ct*h i/ell := by
      have hh := div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos
      linarith
    by_cases hai : a i = 0
    · have hb : B i = 0 := le_antisymm ((hn i).1 hai) (H.B_nonneg i)
      simp [hai, hb]
    · have hap : 0 < a i := lt_of_le_of_ne (ha.1 i) (Ne.symm hai)
      have hF := H.F_pos i _ hap (coordinate_le_one ha i)
      have hgrad := (hn i).2 hap
      have hgrad' := (le_div_iff₀ hF).mp (show -2*(∑ r, B r) ≤
        (C*ell*((∑ r, B r)-(1+ct*h i/ell)*B i/a i))/F i (a i) by
          simpa only [div_mul_eq_mul_div] using hgrad)
      have hgrad'' := mul_le_mul_of_nonneg_right hgrad' hap.le
      have eqn : C*ell*((∑ r, B r)-(1+ct*h i/ell)*B i/a i)*a i =
          C*ell*((∑ r, B r)*a i-(1+ct*h i/ell)*B i) := by field_simp
      rw [eqn] at hgrad''
      apply (mul_le_mul_iff_right₀ (mul_pos hK heta)).mp
      have hr : ell+ct*h i ≠ 0 := (add_pos H.ell_pos (mul_pos H.ct_pos (H.h_pos i))).ne'
      have eqrhs : (C*ell*(1+ct*h i/ell))*((∑ r, B r)*(a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)))) =
          (∑ r, B r)*a i*(C*ell+2*F i (a i)) := by
        field_simp [hr, hK.ne', heta.ne', (multiplier_pos H).ne', H.ell_pos.ne']
      rw [eqrhs]
      nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [← Finset.mul_sum] at hh
  have hstrict := mul_lt_mul_of_pos_left (weighted_deficit H ha) hS
  rw [mul_one] at hstrict
  linarith

theorem minimizing_slope {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) {s : ℝ} (hs : 0 < s) (hsi : s ≤ a i) :
    0 ≤ (g i (a i-s)-g i (a i))/s + (g j (a j+s)-g j (a j))/s + 2*S := by
  have hv := transfer_simplex ha hij hs.le hsi
  have hh : objective g S a₀ a ≤ objective g S a₀ (transfer a i j s) := hm hv
  unfold objective at hh
  rw [transfer_potential g a hij] at hh
  have hb := mul_le_mul_of_nonneg_left (transfer_movement a a₀ hij s) hS
  rw [abs_of_pos hs] at hb
  have hnn : 0 ≤ (g i (a i-s)-g i (a i))+(g j (a j+s)-g j (a j))+2*S*s := by linarith
  have hdiv := div_nonneg hnn hs.le
  convert! hdiv using 1 ; field_simp

theorem right_derivative_nonneg {f : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f d 0) (hmin : ∀ s, 0 < s → s < δ → f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  simp only [Set.mem_Ioi, Set.mem_Iio] at hs hsδ
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (hmin s hs hsδ))

theorem minimum_gradient_difference {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) {di dj : ℝ}
    (hdi : HasDerivAt (g i) di (a i)) (hdj : HasDerivAt (g j) dj (a j)) :
    di-dj ≤ 2*S := by
  have hdi' : HasDerivAt (fun s : ℝ => g i (a i-s)) (-di) 0 := by
    have hd₀ : HasDerivAt (g i) di (a i-id 0) := by simpa using hdi
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_sub (a i))
    convert! hh using 1 ; simp
  have hdj' : HasDerivAt (fun s : ℝ => g j (a j+s)) dj 0 := by
    have hd₀ : HasDerivAt (g j) dj (a j+id 0) := by simpa using hdj
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_add (a j))
    convert! hh using 1 ; simp
  have hd : HasDerivAt (fun s : ℝ => g i (a i-s)+g j (a j+s)+2*S*s) (-di+dj+2*S) 0 := by
    convert! (hdi'.add hdj').add ((hasDerivAt_id 0).const_mul (2*S)) using 1 ; simp
  have hge := right_derivative_nonneg hi hd (fun s hs hsi => ?_)
  · linarith
  have hh := minimizing_slope hS ha hm hij hs hsi.le
  have hh' := mul_nonneg hh hs.le
  simp only [sub_zero, add_zero, mul_zero]
  field_simp at hh'
  linarith

theorem minimum_excludes_singular {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) (hj : a j = 0) {di : ℝ}
    (hdi : HasDerivAt (g i) di (a i))
    (hsing : Tendsto (fun s : ℝ => (g j s-g j 0)/s) (𝓝[>] 0) atBot) : False := by
  have hdi' : HasDerivAt (fun s : ℝ => g i (a i-s)) (-di) 0 := by
    have hd₀ : HasDerivAt (g i) di (a i-id 0) := by simpa using hdi
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_sub (a i))
    convert! hh using 1 ; simp
  have hlim : Tendsto (fun s : ℝ => (g i (a i-s)-g i (a i))/s) (𝓝[>] 0) (𝓝 (-di)) := by
    simpa only [zero_add, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hdi'.tendsto_slope_zero_right
  have hbot := (hlim.add_atBot hsing).atBot_add (tendsto_const_nhds (x := 2*S))
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (g i (a i-s)-g i (a i))/s+(g j s-g j 0)/s+2*S < 0 :=
    hbot.eventually (eventually_lt_atBot 0)
  have hcontra : ∀ᶠ s in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hev, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi)] with s hs hspos hsi
    have hh := minimizing_slope hS ha hm hij hspos hsi.le
    simp only [hj, zero_add] at hh
    linarith
  rcases hcontra.exists with ⟨s, hs⟩
  exact hs

theorem minimum_feasible {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a) :
    ∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i := by
  intro i
  by_contra hbad
  have hb := lt_of_not_ge hbad
  have he : 0 < 1+ct*h i/ell := by
    have hh := div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos
    linarith
  have hS₀ : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => H.B_nonneg i)
  have hprod : 0 < (∑ r, B r)*a i := lt_of_le_of_lt (mul_nonneg he.le (H.B_nonneg i)) hb
  have hi : 0 < a i := pos_of_mul_pos_right hprod hS₀
  have hS : 0 < ∑ i, B i := pos_of_mul_pos_left hprod (ha.1 i)
  have hgi : 0 < (C*ell/F i (a i))*((∑ r, B r)-(1+ct*h i/ell)*B i/a i) := by
    apply mul_pos (div_pos (mul_pos (multiplier_pos H) H.ell_pos) (H.F_pos i _ hi (coordinate_le_one ha i)))
    exact sub_pos.mpr ((div_lt_iff₀ hi).mpr hb)
  obtain ⟨j, hj | hj⟩ := low_coordinate H ha hS
  · have hij : i ≠ j := by intro e; subst j; linarith [hj.1]
    exact minimum_excludes_singular hS₀ ha hm hij hi hj.1
      (H.derivative i _ hi (coordinate_le_one ha i)) (H.inward j hj.2)
  · have hij : i ≠ j := by intro e; subst j; linarith [hj.2]
    have hh := minimum_gradient_difference hS₀ ha hm hij hi
      (H.derivative i _ hi (coordinate_le_one ha i)) (H.derivative j _ hj.1 (coordinate_le_one ha j))
    linarith [hj.2]

/-- Compact minimizing update, with no convexity assumption on the primitives. -/
theorem update (g : ι → ℝ → ℝ) (B h : ι → ℝ)
    (F : ι → ℝ → ℝ) (ell ct C A E : ℝ)
    (H : AnalyticData g B h F ell ct C A E) (a₀ : ι → ℝ) (ha₀ : simplex a₀) :
    ∃ a, simplex a ∧ IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a ∧
      (∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i) ∧
      (∑ i, B i)*movement a a₀ ≤ (∑ i, g i (a₀ i))-(∑ i, g i (a i)) := by
  have hc : ContinuousOn (objective g (∑ i, B i) a₀) {a | simplex a} := by
    apply ContinuousOn.add
    · apply continuousOn_finsetSum
      intro i _
      exact (H.continuous i).comp (continuous_apply i).continuousOn
        (fun a ha => ⟨ha.1 i, coordinate_le_one ha i⟩)
    · unfold movement
      exact Continuous.continuousOn (by fun_prop)
  obtain ⟨a, ha, hm⟩ := simplex_compact.exists_isMinOn ⟨a₀, ha₀⟩ hc
  refine ⟨a, ha, hm, minimum_feasible H ha hm, ?_⟩
  have hh : objective g (∑ i, B i) a₀ a ≤ objective g (∑ i, B i) a₀ a₀ := hm ha₀
  simp only [objective, movement, sub_self, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hh ⊢
  linarith

end UniformKServer.SimplexTracker


end OAI
