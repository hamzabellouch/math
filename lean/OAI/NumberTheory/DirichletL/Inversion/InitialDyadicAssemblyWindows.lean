import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_smooth (i:Fin 4) : ContDiff ℝ ∞ (cutoff i) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

theorem cutoff_norm_le (i:Fin 4)(x:ℝ) : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support (i:Fin 4) :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simpa only [Function.mem_support,cutoff,ne_eq,Complex.ofReal_eq_zero] using hx
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem cutoff_tsupport (i:Fin 4) :
    tsupport (cutoff i)⊆Set.Icc (1/4:ℝ) 1 :=
  closure_minimal (fun _ hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx)) isClosed_Icc

theorem cutoff_eventual_width (η:ℝ)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀i:Fin 4,
      tsupport (cutoff i)⊆Set.Icc (Z^(-η)) (Z^η) := by
  have ht:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro i x hx
  have hs:=cutoff_tsupport i hx
  have hlo:Z^(-η)≤(1/4:ℝ) := by
    rw [Real.rpow_neg (by positivity)]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) ht
  exact ⟨hlo.trans hs.1,hs.2.trans (by linarith)⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
    (k:ℤ)(hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper (C η:ℝ)(_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  calc
    dyadicScale k≤4*b:=hs
    _≤4*(C*Z^R):=mul_le_mul_of_nonneg_left hbR (by norm_num)
    _=(4*C)*Z^R:=by ring
    _≤Z^η*Z^R:=mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
    _=Z^R*Z^η:=mul_comm _ _

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
