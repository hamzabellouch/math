import Mathlib
import OAI.Probability.SKValue.Equations.ProfileShape

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
noncomputable def heatDen (a t : ℝ) : ℝ := a+max 0 t
noncomputable def heatScale (a t : ℝ) : ℝ := a/heatDen a t
noncomputable def heatTime (a t : ℝ) : ℝ := a-a^2/heatDen a t

lemma heatDen_pos {a : ℝ} (ha : 0<a) (t : ℝ) : 0<heatDen a t :=
  add_pos_of_pos_of_nonneg ha (le_max_left _ _)
lemma heatDen_of_nonneg (a : ℝ) {t : ℝ} (ht : 0≤t) : heatDen a t=a+t := by
  simp only [heatDen,max_eq_right ht]
lemma heatScale_mem {a : ℝ} (ha : 0<a) (t : ℝ) : heatScale a t∈Icc (0:ℝ) 1 := by
  constructor
  · exact (div_pos ha (heatDen_pos ha t)).le
  · exact (div_le_one (heatDen_pos ha t)).mpr (by dsimp [heatDen]; linarith [le_max_left (0:ℝ) t])
lemma heatTime_pos {a t : ℝ} (ha : 0<a) (ht : 0<t) : 0<heatTime a t := by
  dsimp [heatTime]
  rw [heatDen_of_nonneg a ht.le]
  rw [sub_pos,div_lt_iff₀ (add_pos ha ht)]
  nlinarith
lemma heatDen_continuous (a : ℝ) : Continuous (heatDen a) := continuous_const.add (continuous_const.max continuous_id)
lemma heatScale_continuous {a : ℝ} (ha : 0<a) : Continuous (heatScale a) :=
  continuous_const.div (heatDen_continuous a) (fun t ↦ (heatDen_pos ha t).ne')
lemma heatTime_continuous {a : ℝ} (ha : 0<a) : Continuous (heatTime a) :=
  continuous_const.sub (continuous_const.div (heatDen_continuous a) (fun t ↦ (heatDen_pos ha t).ne'))
lemma heatDen_hasDerivAt {a t : ℝ} (ht : 0<t) : HasDerivAt (heatDen a) 1 t := by
  apply ((hasDerivAt_id t).const_add a).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact heatDen_of_nonneg a hs.le
lemma heatScale_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (heatScale a) (-heatScale a t/heatDen a t) t := by
  convert! (hasDerivAt_const t a).div (heatDen_hasDerivAt ht) (heatDen_pos ha t).ne' using 1
  dsimp [heatScale]; field_simp; ring
lemma heatTime_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (heatTime a) ((heatScale a t)^2) t := by
  convert! (hasDerivAt_const t a).sub
    ((hasDerivAt_const t (a^2)).div (heatDen_hasDerivAt ht) (heatDen_pos ha t).ne') using 1
  dsimp [heatScale]; field_simp; ring

lemma scaledHeatJet_moving {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c a t : ℝ}
    (hc : 0<c) (ha : 0<a) (ht : 0<t) (n : ℕ) (x : ℝ)
    (F : ℝ → ℝ → ℝ) (hF : Continuous (fun p : ℝ×ℝ ↦ F p.1 p.2))
    (hft : ∀ s,0<s → ∀ y,HasDerivAt (scaledHeatJet c ψ n · y) (F s y) s) :
    HasDerivAt (fun s ↦ scaledHeatJet c ψ n (heatTime a s) (heatScale a s*x))
      (F (heatTime a t) (heatScale a t*x)*(heatScale a t)^2-
        scaledHeatJet c ψ (n+1) (heatTime a t) (heatScale a t*x)*heatScale a t/heatDen a t*x) t := by
  have hp := heatTime_hasDerivAt ha ht
  have hq := (heatScale_hasDerivAt ha ht).mul_const x
  have hh := moving_partial_deriv
    (f := scaledHeatJet c ψ n) (ft := F) (fx := scaledHeatJet c ψ (n+1))
    (p := heatTime a) (q := fun s ↦ heatScale a s*x)
    (by
      filter_upwards [(continuous_fst.tendsto (heatTime a t,heatScale a t*x)).eventually
        (Ioi_mem_nhds (heatTime_pos ha ht))] with z hz
      exact hft z.1 hz z.2)
    (Filter.Eventually.of_forall (fun z ↦ scaledHeatJet_space hψ hc.le n z.1 z.2))
    hF.continuousAt (scaledHeatJet_continuous hψ hc.le (n+1)).continuousAt hp hq
  convert! hh using 1
  ring

noncomputable def forwardJet (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  (if n=0 then x/heatDen a t else if n=1 then 1/heatDen a t else 0)-
    (heatScale a t)^(n+1)*scaledHeatJet c ψ n (heatTime a t) (heatScale a t*x)
lemma forwardJet_zero (a c : ℝ) (ψ : ℝ → ℝ) (t x : ℝ) :
    forwardJet a c ψ 0 t x=x/heatDen a t-
      heatScale a t*scaledHeatJet c ψ 0 (heatTime a t) (heatScale a t*x) := by simp [forwardJet]
lemma forwardJet_one (a c : ℝ) (ψ : ℝ → ℝ) (t x : ℝ) :
    forwardJet a c ψ 1 t x=1/heatDen a t-
      (heatScale a t)^2*scaledHeatJet c ψ 1 (heatTime a t) (heatScale a t*x) := by simp [forwardJet]
lemma forwardJet_succ_succ (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (t x : ℝ) :
    forwardJet a c ψ (n+2) t x= -(heatScale a t)^(n+3)*scaledHeatJet c ψ (n+2) (heatTime a t) (heatScale a t*x) := by
  simp [forwardJet,Nat.add_assoc,neg_mul]
lemma forwardJet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0≤c) (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ forwardJet a c ψ n p.1 p.2) := by
  have h1 : Continuous (fun p : ℝ×ℝ ↦ heatDen a p.1) := (heatDen_continuous a).comp continuous_fst
  have h2 : Continuous (fun p : ℝ×ℝ ↦ heatScale a p.1) := (heatScale_continuous ha).comp continuous_fst
  have h3 : Continuous (fun p : ℝ×ℝ ↦ heatTime a p.1) := (heatTime_continuous ha).comp continuous_fst
  have h4 := (scaledHeatJet_continuous hψ hc n).comp (h3.prodMk (h2.mul continuous_snd))
  dsimp only [forwardJet]
  split_ifs <;> fun_prop (disch := intro p; exact (heatDen_pos ha p.1).ne')
lemma forwardJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (hc : 0≤c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (forwardJet a c ψ n t) (forwardJet a c ψ (n+1) t x) x := by
  have hd := ((scaledHeatJet_space hψ hc n (heatTime a t) (heatScale a t*x)).comp x
    ((hasDerivAt_id x).const_mul (heatScale a t))).const_mul ((heatScale a t)^(n+1))
  obtain rfl | n := n
  · convert! ((hasDerivAt_id x).div_const (heatDen a t)).sub hd using 1
    simp [forwardJet]
    ring
  obtain rfl | n := n
  · convert! (hasDerivAt_const x (1/heatDen a t)).sub hd using 1
    simp [forwardJet]
    ring
  · convert! hd.neg using 1
    · funext y; simp [forwardJet,pow_succ]
    · simp [forwardJet,pow_succ]; ring
end SKValue

end

section

open Set Filter
open scoped Topology
namespace SKValue
lemma abs_sub_upper (x y : ℝ) : |x-y|≤|x|+|y| := by
  simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x 0 y
lemma heatDen_inv_hasDerivAt {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    HasDerivAt (fun s ↦ 1/heatDen a s) (-(1/heatDen a t)^2) t := by
  convert! (heatDen_hasDerivAt ht).inv (heatDen_pos ha t).ne' using 1
  · funext s; simp only [one_div,Pi.inv_apply]
  · simp only [one_div,inv_pow]; ring

lemma forwardJet_time0 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0<c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 0 · x)
      ((1/2:ℝ)*forwardJet a c ψ 2 t x-forwardJet a c ψ 0 t x*forwardJet a c ψ 1 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 0 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 2 s y+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 1 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time0 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := ((heatDen_inv_hasDerivAt ha ht).const_mul x).sub (hl.mul hm)
  convert! hh using 1
  · funext s; simp [forwardJet,div_eq_mul_inv]
  · simp only [forwardJet,ite_true,ite_false,show (1:ℕ)≠0 by omega,
      show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega]
    norm_num
    simp only [div_eq_mul_inv]
    ring

lemma forwardJet_time1 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0<c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 1 · x)
      ((1/2:ℝ)*forwardJet a c ψ 3 t x-(forwardJet a c ψ 1 t x)^2-forwardJet a c ψ 0 t x*forwardJet a c ψ 2 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 1 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 3 s y+(scaledHeatJet c ψ 1 s y)^2+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 2 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time1 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := (heatDen_inv_hasDerivAt ha ht).sub ((hl.pow 2).mul hm)
  convert! hh using 1
  simp [forwardJet,div_eq_mul_inv]
  ring

lemma forwardJet_time2 {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c t : ℝ}
    (ha : 0<a) (hc : 0<c) (ht : 0<t) (x : ℝ) :
    HasDerivAt (forwardJet a c ψ 2 · x)
      ((1/2:ℝ)*forwardJet a c ψ 4 t x-3*forwardJet a c ψ 1 t x*forwardJet a c ψ 2 t x-forwardJet a c ψ 0 t x*forwardJet a c ψ 3 t x) t := by
  have hm := scaledHeatJet_moving hψ hc ha ht 2 x
    (fun s y ↦ (1/2:ℝ)*scaledHeatJet c ψ 4 s y+3*scaledHeatJet c ψ 1 s y*scaledHeatJet c ψ 2 s y+scaledHeatJet c ψ 0 s y*scaledHeatJet c ψ 3 s y)
    (by
      have h0 := scaledHeatJet_continuous hψ hc.le 0
      have h1 := scaledHeatJet_continuous hψ hc.le 1
      have h2 := scaledHeatJet_continuous hψ hc.le 2
      have h3 := scaledHeatJet_continuous hψ hc.le 3
      have h4 := scaledHeatJet_continuous hψ hc.le 4
      fun_prop)
    (fun s hs y ↦ scaledHeatJet_time2 hψ hc hs y)
  have hl := heatScale_hasDerivAt ha ht
  have hh := ((hl.pow 3).mul hm).neg
  convert! hh using 1
  · funext s; simp [forwardJet]
  · simp only [forwardJet,ite_true,ite_false,show (1:ℕ)≠0 by omega,
      show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,
      show (3:ℕ)≠0 by omega,show (3:ℕ)≠1 by omega,
      show (4:ℕ)≠0 by omega,show (4:ℕ)≠1 by omega]
    norm_num
    simp only [div_eq_mul_inv]
    ring
lemma heatDen_inv_bound {a : ℝ} (ha : 0<a) (t : ℝ) :
    0≤1/heatDen a t ∧ 1/heatDen a t≤1/a := by
  refine ⟨one_div_nonneg.mpr (heatDen_pos ha t).le,?_⟩
  exact one_div_le_one_div_of_le ha (by dsimp [heatDen]; linarith [le_max_left (0:ℝ) t])

lemma forwardJet_bound {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0<c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|forwardJet a c ψ (n+1) t x|≤C := by
  obtain ⟨C,hC,hb⟩ := scaledHeatJet_bound hψ hc (n+1)
  refine ⟨1/a+C,by positivity,?_⟩
  intro t x
  have hs := heatScale_mem ha t
  have hh : |(heatScale a t)^(n+1+1)*scaledHeatJet c ψ (n+1) (heatTime a t) (heatScale a t*x)|≤C := by
    rw [abs_mul,abs_pow,abs_of_nonneg hs.1]
    calc
      _ ≤ 1*C := mul_le_mul (pow_le_one₀ hs.1 hs.2) (hb _ _) (abs_nonneg _) (by norm_num)
      _ = C := one_mul _
  have hi := heatDen_inv_bound ha t
  calc
    _ ≤ |if n+1=0 then x/heatDen a t else if n+1=1 then 1/heatDen a t else 0|+C :=
      (abs_sub_upper _ _).trans (add_le_add le_rfl hh)
    _ ≤ 1/a+C := by
      simp only [Nat.add_one_ne_zero,ite_false]
      split_ifs <;> simp only [abs_of_nonneg hi.1,abs_zero] <;> linarith [one_div_nonneg.mpr ha.le]

lemma forwardJet_growth {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {a c : ℝ}
    (ha : 0<a) (hc : 0<c) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|forwardJet a c ψ 0 t x|≤C*(1+|x|) := by
  obtain ⟨C,hC,hb⟩ := scaledHeatJet_bound hψ hc 0
  refine ⟨1/a+C,by positivity,?_⟩
  intro t x
  have hs := heatScale_mem ha t
  have hi := heatDen_inv_bound ha t
  have hh : |heatScale a t*scaledHeatJet c ψ 0 (heatTime a t) (heatScale a t*x)|≤C := by
    rw [abs_mul,abs_of_nonneg hs.1]
    calc
      _ ≤ 1*C := mul_le_mul hs.2 (hb _ _) (abs_nonneg _) (by norm_num)
      _ = C := one_mul _
  rw [forwardJet_zero]
  calc
    _ ≤ |x/heatDen a t|+C := (abs_sub_upper _ _).trans (add_le_add le_rfl hh)
    _ = |x| *(1/heatDen a t)+C := by rw [abs_div,abs_of_pos (heatDen_pos ha t)]; ring
    _ ≤ |x| *(1/a)+C := add_le_add (mul_le_mul_of_nonneg_left hi.2 (abs_nonneg x)) le_rfl
    _ ≤ (1/a+C)*(1+|x|) := by nlinarith [mul_nonneg hC (abs_nonneg x),one_div_nonneg.mpr ha.le]

noncomputable def SmoothTerminal.forwardBurgers {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (heven : ∀ x,ψ (-x)=ψ x) {a c : ℝ} (ha : 0<a) (hc : 0<c) (T : ℝ) : ForwardBurgers T where
  jet := forwardJet a c ψ
  continuous := forwardJet_continuous hψ ha hc.le
  space := forwardJet_space hψ hc.le
  time0 := fun _ ht x ↦ forwardJet_time0 hψ ha hc ht.1 x
  time1 := fun _ ht x ↦ forwardJet_time1 hψ ha hc ht.1 x
  time2 := fun _ ht x ↦ forwardJet_time2 hψ ha hc ht.1 x
  bound := by
    intro n
    obtain ⟨C,hC,hb⟩ := forwardJet_bound hψ ha hc n
    exact ⟨C,hC,fun t ht x ↦ hb t x⟩
  growth := by
    obtain ⟨C,hC,hb⟩ := forwardJet_growth hψ ha hc
    exact ⟨C,hC,fun t ht x ↦ hb t x⟩
  zero0 := by
    intro t
    simp only [forwardJet_zero,mul_zero,zero_div,scaledHeatJet,iteratedDeriv_zero,
      deriv_even_zero (coleHopf_even heven c _),sub_zero]
  zero2 := by
    intro t
    simp only [forwardJet_succ_succ,mul_zero,scaledHeatJet,
      even_third_deriv_zero (coleHopf_even heven c _)]

end SKValue

end

end OAI
