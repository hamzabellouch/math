import OAI.NumberTheory.Ostmann.Supply.ContractingKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
variable {p : ℕ} [NeZero p]

def unitKernelGenerating (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) : ℂ :=
  (∑x∈Finset.univ.erase 0,(1+u*(localKernel S t x:ℂ))*(1+v*(localKernel S t x:ℂ)))/((p:ℂ)-1)

theorem unitKernelGenerating_expansion (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ)
    (hp : 2≤p) :
    unitKernelGenerating S t u v = 1+(u+v)*
      ((-(t*((largeSpectrum S).card:ℝ)/p)/((p:ℝ)-1):ℝ):ℂ)+
      (u*v)*((t^2*(((largeSpectrum S).card:ℝ)/p-(((largeSpectrum S).card:ℝ)/p)^2)/
        ((p:ℝ)-1):ℝ):ℂ) := by
  have hcard : ((Finset.univ.erase (0:ZMod p)).card:ℂ) = (p:ℂ)-1 := by
    simp [Finset.card_erase_of_mem,ZMod.card,Nat.cast_sub (show 1≤p by omega)]
  have hpn : (p:ℂ)-1≠0 := by
    have hpr : (2:ℝ)≤p := by exact_mod_cast hp
    exact_mod_cast (show (p:ℝ)-1≠0 by linarith)
  have hex (b : ℂ) : (1+u*b)*(1+v*b)=1+(u+v)*b+(u*v)*b^2 := by ring
  unfold unitKernelGenerating
  simp only [hex,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,
    ←Finset.mul_sum,←Complex.ofReal_pow,←Complex.ofReal_sum,hcard,
    localKernel_nonzero_sum,localKernel_nonzero_sum_sq]
  push_cast
  field_simp

theorem unitKernelGenerating_one (S : Finset (ZMod p)) (t : ℝ) :
    unitKernelGenerating S t 1 1=(unitKernelMean S t:ℂ) := by
  unfold unitKernelGenerating unitKernelMean
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem sparse_unit_moment_bounds (S : Finset (ZMod p)) {ε t : ℝ}
    (hp : 2≤p) (ht : 0≤t) (ht1 : t≤1) (heps : 0≤ε)
    (hE : ((largeSpectrum S).card:ℝ)/p≤ε) :
    |-(t*((largeSpectrum S).card:ℝ)/p)/((p:ℝ)-1)| ≤ 2*ε/(p:ℝ) ∧
    |t^2*(((largeSpectrum S).card:ℝ)/p-(((largeSpectrum S).card:ℝ)/p)^2)/
      ((p:ℝ)-1)| ≤ 2*ε/(p:ℝ) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hpm : 0<(p:ℝ)-1 := by linarith
  let e : ℝ := ((largeSpectrum S).card:ℝ)/p
  have he0 : 0≤e := div_nonneg (Nat.cast_nonneg _) hp0.le
  have he1 : e≤1 := by
    have hc : (largeSpectrum S).card≤p := by
      simpa only [ZMod.card] using Finset.card_le_univ (largeSpectrum S)
    exact (div_le_one hp0).mpr (by exact_mod_cast hc)
  have hm : ε/((p:ℝ)-1)≤2*ε/(p:ℝ) := by
    apply (div_le_div_iff₀ hpm hp0).mpr
    nlinarith
  have hsq : 0≤e-e^2 := by nlinarith
  have htSq : t^2≤1 := by nlinarith
  constructor
  · have hte : t*e≤ε := (mul_le_mul_of_nonneg_right ht1 he0).trans (by simpa using hE)
    calc
      _ = t*e/((p:ℝ)-1) := by
        rw [abs_div,abs_neg,abs_of_nonneg (by positivity),abs_of_pos hpm]
        dsimp [e]
        ring
      _ ≤ ε/((p:ℝ)-1) := div_le_div_of_nonneg_right hte hpm.le
      _ ≤ _ := hm
  · change |t^2*(e-e^2)/((p:ℝ)-1)|≤_
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hsq) hpm.le)]
    apply (div_le_div_of_nonneg_right _ hpm.le).trans hm
    exact (mul_le_mul_of_nonneg_right htSq hsq).trans (by nlinarith [hE])

theorem sparse_unitKernelGenerating_norm (S : Finset (ZMod p)) (u v : ℂ)
    (hp : 2≤p) (hlo : (1/3:ℝ)≤density S) (hhi : density S≤2/3)
    (hg : gamma S ≤ supplyEpsilon^2) (hu : ‖u‖≤103/100) (hv : ‖v‖≤103/100) :
    ‖unitKernelGenerating S sparseKernelScale u v‖≤1+8*supplyEpsilon/(p:ℝ) := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hE := (sparse_transform_concentration S (by linarith) (by linarith)
    supplyEpsilon_pos.le supplyEpsilon_le_one hg).1
  have hm := sparse_unit_moment_bounds S hp sparseKernelScale_nonneg sparseKernelScale_le_one
    supplyEpsilon_pos.le ((div_le_iff₀ hp0).mpr hE)
  rw [unitKernelGenerating_expansion S sparseKernelScale u v hp]
  have huv : ‖u+v‖≤206/100 := (norm_add_le u v).trans (by linarith)
  have huv2 : ‖u*v‖≤11/10 := by
    rw [norm_mul]
    nlinarith [norm_nonneg u,norm_nonneg v,mul_nonneg
      (show 0≤(103/100:ℝ)-‖u‖ by linarith) (show 0≤(103/100:ℝ)-‖v‖ by linarith)]
  calc
    _ ≤ 1+‖u+v‖*|-(sparseKernelScale*((largeSpectrum S).card:ℝ)/p)/((p:ℝ)-1)|+
        ‖u*v‖*|sparseKernelScale^2*(((largeSpectrum S).card:ℝ)/p-
          (((largeSpectrum S).card:ℝ)/p)^2)/((p:ℝ)-1)| := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (by simp only [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact le_rfl))
        (by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]; exact le_rfl))
    _ ≤ 1+(206/100:ℝ)*(2*supplyEpsilon/(p:ℝ))+(11/10:ℝ)*(2*supplyEpsilon/(p:ℝ)) := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul huv hm.1 (abs_nonneg _) (by norm_num)))
        (mul_le_mul huv2 hm.2 (abs_nonneg _) (by norm_num))
    _ ≤ _ := by
      have he : (206/100:ℝ)*2*supplyEpsilon+(11/10:ℝ)*2*supplyEpsilon ≤ 8*supplyEpsilon := by
        have heps := supplyEpsilon_pos; nlinarith
      have hh := div_le_div_of_nonneg_right he hp0.le
      simp only [add_div,mul_div_assoc] at hh
      convert add_le_add_left hh 1 using 1 <;> ring

end Ostmann.Supply

end

end OAI
