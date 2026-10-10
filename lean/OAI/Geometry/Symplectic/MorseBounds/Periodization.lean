import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.Periodization
open scoped Manifold ContDiff Topology
noncomputable section
open Function Set

def rho (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

def periodicHamiltonian {M : Type*} (L : ℝ × M → ℝ) (q : ℝ × M) : ℝ :=
  deriv rho (Int.fract q.1) * L (rho (Int.fract q.1), q.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
local notation "I" => 𝓘(ℝ, E)

def periodizedFlow (e : M ≃ₘ⟮I, I⟯ M) (g : ℝ × M → M) (q : ℝ × M) : M :=
  g (rho (Int.fract q.1), (e.toEquiv ^ Int.floor q.1) q.2)

def periodizedVector (V : ℝ → (x : M) → TangentSpace I x) (t : ℝ) (x : M) :
    TangentSpace I x := deriv rho (Int.fract t) • V (rho (Int.fract t)) x

lemma rho_smooth : ContDiff ℝ ∞ rho :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma rho_deriv_smooth : ContDiff ℝ ∞ (deriv rho) := (contDiff_infty_iff_deriv.mp rho_smooth).2

lemma rho_zero {t : ℝ} (ht : t ≤ 1 / 3) : rho t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma rho_one {t : ℝ} (ht : 2 / 3 ≤ t) : rho t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma rho_deriv_zero {t : ℝ} (ht : t < 1 / 3 ∨ 2 / 3 < t) : deriv rho t = 0 := by
  rcases ht with ht | ht
  · have he : rho =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact rho_zero hs.le
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he |>.deriv
  · have he : rho =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact rho_one hs.le
    exact (hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he |>.deriv

lemma floor_on_cell (n : ℤ) {t : ℝ} (ht : t ∈ Ico (n:ℝ) (n+1)) :
    Int.floor t = n := Int.floor_eq_iff.mpr ht

lemma fract_on_cell (n : ℤ) {t : ℝ} (ht : t ∈ Ico (n:ℝ) (n+1)) :
    Int.fract t = t - n := by rw [Int.fract, floor_on_cell n ht]

lemma floor_near_seam (n : ℤ) {t : ℝ} (ht : t ∈ Ioo ((n:ℝ)-1/4) (n+1/4)) :
    (t < n ∧ Int.floor t = n-1 ∧ 2/3 < Int.fract t) ∨
    ((n:ℝ) ≤ t ∧ Int.floor t = n ∧ Int.fract t < 1/3) := by
  by_cases hn : t < n
  · have hf : Int.floor t = n-1 := Int.floor_eq_iff.mpr (by
      push_cast
      constructor <;> linarith [ht.1])
    exact Or.inl ⟨hn, hf, by rw [Int.fract, hf]; push_cast; linarith [ht.1]⟩
  · have hf : Int.floor t = n := Int.floor_eq_iff.mpr ⟨le_of_not_gt hn, by linarith [ht.2]⟩
    exact Or.inr ⟨le_of_not_gt hn, hf, by rw [Int.fract, hf]; linarith [ht.2]⟩

omit [TopologicalSpace M] in
lemma hamiltonian_near_seam (L : ℝ × M → ℝ) (n : ℤ) {t : ℝ}
    (ht : t ∈ Ioo ((n:ℝ)-1/4) (n+1/4)) (x : M) : periodicHamiltonian L (t,x) = 0 := by
  have hd : deriv rho (Int.fract t) = 0 := by
    rcases floor_near_seam n ht with ⟨_,_,h⟩ | ⟨_,_,h⟩
    · exact rho_deriv_zero (Or.inr h)
    · exact rho_deriv_zero (Or.inl h)
  simp [periodicHamiltonian, hd]

lemma flow_near_seam (e : M ≃ₘ⟮I, I⟯ M) (g : ℝ × M → M)
    (h0 : ∀ x, g (0,x) = x) (h1 : ∀ x, g (1,x) = e x)
    (n : ℤ) {t : ℝ} (ht : t ∈ Ioo ((n:ℝ)-1/4) (n+1/4)) (x : M) :
    periodizedFlow e g (t,x) = (e.toEquiv ^ n) x := by
  rcases floor_near_seam n ht with ⟨_,hf,hr⟩ | ⟨_,hf,hr⟩
  · simp only [periodizedFlow, hf, rho_one hr.le, h1]
    change ((e.toEquiv : Equiv.Perm M) * e.toEquiv ^ (n-1)) x = _
    rw [← zpow_one_add]
    congr 2; ring
  · simp [periodizedFlow, hf, rho_zero hr.le, h0]

lemma endpoint_power_smooth (e : M ≃ₘ⟮I, I⟯ M) (n : ℤ) :
    ContMDiff I I ∞ ((e.toEquiv ^ n : Equiv.Perm M) : M → M) := by
  apply zpow_induction_left (P := fun f : Equiv.Perm M => ContMDiff I I ∞ (f : M → M))
  · exact contMDiff_id
  · intro a ha
    exact e.contMDiff.comp ha
  · intro a ha
    exact e.symm.contMDiff.comp ha

theorem periodicHamiltonian_smooth (L : ℝ × M → ℝ)
    (hL : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ L) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (periodicHamiltonian L) := by
  intro q
  let n : ℤ := Int.floor q.1
  by_cases he : q.1 = (n:ℝ)
  · have hn : ∀ᶠ q' : ℝ × M in 𝓝 q, q'.1 ∈ Ioo ((n:ℝ)-1/4) (n+1/4) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds (by simp only [mem_preimage]; rw [he]; constructor <;> linarith)
    apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q' hq'
    exact hamiltonian_near_seam L n hq' q'.2
  · have hcell : q.1 ∈ Ioo (n:ℝ) (n+1) :=
      ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm he), Int.lt_floor_add_one _⟩
    have hn : ∀ᶠ q' : ℝ × M in 𝓝 q, q'.1 ∈ Ioo (n:ℝ) (n+1) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds hcell
    have hs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun q' : ℝ × M => q'.1 - n) :=
      contMDiff_fst.sub contMDiff_const
    have hr := rho_smooth.contMDiff.comp hs
    have hrd := rho_deriv_smooth.contMDiff.comp hs
    have htotal := hrd.mul (hL.comp (hr.prodMk contMDiff_snd))
    apply (htotal q).congr_of_eventuallyEq
    filter_upwards [hn] with q' hq'
    simp only [periodicHamiltonian, fract_on_cell n ⟨hq'.1.le,hq'.2⟩, Function.comp_apply, Pi.mul_apply]

omit [TopologicalSpace M] in
theorem periodicHamiltonian_periodic (L : ℝ × M → ℝ) (t : ℝ) (x : M) :
    periodicHamiltonian L (t + 1, x) = periodicHamiltonian L (t, x) := by
  simp [periodicHamiltonian, Int.fract_add_one]

theorem periodizedFlow_smooth (e : M ≃ₘ⟮I, I⟯ M) (g : ℝ × M → M)
    (hg : ContMDiff (𝓘(ℝ).prod I) I ∞ g)
    (h0 : ∀ x, g (0,x) = x) (h1 : ∀ x, g (1,x) = e x) :
    ContMDiff (𝓘(ℝ).prod I) I ∞ (periodizedFlow e g) := by
  intro q
  let n : ℤ := Int.floor q.1
  by_cases he : q.1 = (n:ℝ)
  · have hn : ∀ᶠ q' : ℝ × M in 𝓝 q, q'.1 ∈ Ioo ((n:ℝ)-1/4) (n+1/4) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds (by simp only [mem_preimage]; rw [he]; constructor <;> linarith)
    have hpow : ContMDiff (𝓘(ℝ).prod I) I ∞
        (fun q' : ℝ × M => (e.toEquiv ^ n) q'.2) :=
      (endpoint_power_smooth e n).comp contMDiff_snd
    apply (hpow q).congr_of_eventuallyEq
    filter_upwards [hn] with q' hq'
    exact flow_near_seam e g h0 h1 n hq' q'.2
  · have hcell : q.1 ∈ Ioo (n:ℝ) (n+1) :=
      ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm he), Int.lt_floor_add_one _⟩
    have hn : ∀ᶠ q' : ℝ × M in 𝓝 q, q'.1 ∈ Ioo (n:ℝ) (n+1) :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds hcell
    have hs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (fun q' : ℝ × M => q'.1 - n) :=
      contMDiff_fst.sub contMDiff_const
    have hr := rho_smooth.contMDiff.comp hs
    have hpow : ContMDiff (𝓘(ℝ).prod I) I ∞
        (fun q' : ℝ × M => (e.toEquiv ^ n) q'.2) :=
      (endpoint_power_smooth e n).comp contMDiff_snd
    have htotal := hg.comp (hr.prodMk hpow)
    apply (htotal q).congr_of_eventuallyEq
    filter_upwards [hn] with q' hq'
    simp only [periodizedFlow, floor_on_cell n ⟨hq'.1.le,hq'.2⟩,
      fract_on_cell n ⟨hq'.1.le,hq'.2⟩, Function.comp_apply]

theorem periodizedFlow_endpoints (e : M ≃ₘ⟮I, I⟯ M) (g : ℝ × M → M)
    (h0 : ∀ x, g (0,x) = x) :
    (∀ x, periodizedFlow e g (0,x) = x) ∧
    (∀ x, periodizedFlow e g (1,x) = e x) := by
  have hr : rho 0 = 0 := rho_zero (by norm_num)
  constructor <;> intro x <;> simp [periodizedFlow, hr, h0]

lemma reparam_ode (g : ℝ × M → M) (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => g (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (g (t,x)))))
    (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun s => g (a s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv a t • V (a t) (g (a t,x)))) := by
  have ha' : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) a t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv a t)) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert ha.hasDerivAt.hasFDerivAt using 1; rfl
  have hh : HasMFDerivAt 𝓘(ℝ) I (fun s => g (a s,x)) t
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (V (a t) (g (a t,x)))).comp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv a t))) := by
    convert (hV (a t) x).comp t ha' using 1 <;> rfl
  have hc : ((ContinuousLinearMap.id ℝ ℝ).smulRight (V (a t) (g (a t,x)))).comp
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv a t)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (deriv a t • V (a t) (g (a t,x))) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, smul_smul, smul_eq_mul]
  erw [hc] at hh
  exact hh

theorem periodizedFlow_ode (e : M ≃ₘ⟮I, I⟯ M) (g : ℝ × M → M)
    (h0 : ∀ x, g (0,x) = x) (h1 : ∀ x, g (1,x) = e x)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => g (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (g (t,x))))) :
    ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => periodizedFlow e g (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (periodizedVector V t (periodizedFlow e g (t,x)))) := by
  intro t x
  let n : ℤ := Int.floor t
  by_cases he : t = (n:ℝ)
  · have hn : ∀ᶠ s : ℝ in 𝓝 t, s ∈ Ioo ((n:ℝ)-1/4) (n+1/4) :=
      isOpen_Ioo.mem_nhds (by rw [he]; constructor <;> linarith)
    have heq : (fun s => periodizedFlow e g (s,x)) =ᶠ[𝓝 t] fun _ => (e.toEquiv ^ n) x := by
      filter_upwards [hn] with s hs
      exact flow_near_seam e g h0 h1 n hs x
    have hd : deriv rho (Int.fract t) = 0 := by
      rw [he, Int.fract_intCast]
      exact rho_deriv_zero (Or.inl (by norm_num))
    have hc : HasMFDerivAt 𝓘(ℝ) I (fun _ : ℝ => (e.toEquiv ^ n) x) t 0 :=
      hasMFDerivAt_const _ _
    simp only [periodizedVector, hd, zero_smul, ContinuousLinearMap.smulRight_zero]
    convert hc.congr_of_eventuallyEq heq using 1; rfl
  · have hcell : t ∈ Ioo (n:ℝ) (n+1) :=
      ⟨lt_of_le_of_ne (Int.floor_le _) (Ne.symm he), Int.lt_floor_add_one _⟩
    have hn : ∀ᶠ s : ℝ in 𝓝 t, s ∈ Ioo (n:ℝ) (n+1) := isOpen_Ioo.mem_nhds hcell
    have heq : (fun s => periodizedFlow e g (s,x)) =ᶠ[𝓝 t]
        (fun s => g (rho (s-n), (e.toEquiv ^ n) x)) := by
      filter_upwards [hn] with s hs
      simp only [periodizedFlow, floor_on_cell n ⟨hs.1.le,hs.2⟩, fract_on_cell n ⟨hs.1.le,hs.2⟩]
    have ha : DifferentiableAt ℝ (fun s : ℝ => rho (s-n)) t :=
      (rho_smooth.differentiable (by simp) _).comp t ((differentiableAt_id).sub_const _)
    have hdr : deriv (fun s : ℝ => rho (s-n)) t = deriv rho (t-n) := by
      have hh := (rho_smooth.differentiable (by simp) (t-n)).hasDerivAt.comp t
        ((hasDerivAt_id t).sub_const (n:ℝ))
      convert hh.deriv using 1 <;> simp only [Function.comp_def, id_eq, mul_one]
    have hh := (reparam_ode g V hV (fun s => rho (s-n)) t ha ((e.toEquiv ^ n) x)).congr_of_eventuallyEq heq
    simp only [periodizedVector, fract_on_cell n ⟨hcell.1.le,hcell.2⟩]
    rw [hdr] at hh
    have hval := heq.eq_of_nhds
    rw [hval]
    convert hh using 1; rfl

theorem periodizedVector_hamiltonian
    (w : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (L : ℝ × M → ℝ) (hL : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ L)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ∀ t x, w x (V t x) = mvfderiv I (fun y => L (t,y)) x) :
    ∀ t x, w x (periodizedVector V t x) =
      mvfderiv I (fun y => periodicHamiltonian L (t,y)) x := by
  intro t x
  have hh : MDifferentiableAt I 𝓘(ℝ) (fun y => L (rho (Int.fract t),y)) x :=
    (hL.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) x
  simp only [periodizedVector, map_smul, hV, periodicHamiltonian]
  rw [mvfderiv_fun_mul mdifferentiableAt_const hh, mvfderiv_const, smul_zero, add_zero]

end
end MorseArnold.Periodization

end

end OAI
