import OAI.Analysis.AncientFlat.Regularity.UnitInterpolation
import OAI.Analysis.AncientFlat.Evolution.DilationDerivatives

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior ClassicalIBP ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def window (p0 : V × ℝ) (q : ℝ) (p : V × ℝ) : V × ℝ :=
  (p0.1+q • p.1,p0.2+q^4*p.2)
def windowValue (p0 : V × ℝ) (q : ℝ) (u : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => u (p0.2+q^4*t) (p0.1+q • x)
def windowTime (p0 : V × ℝ) (q : ℝ) (ut : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => q^4 • ut (p0.2+q^4*t) (p0.1+q • x)
lemma pow_four_quarter {q : ℝ} (hq : 0≤q) : (q^4)^((1:ℝ)/4)=q := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hq]
  norm_num
omit [FiniteDimensional ℝ V] in
lemma pdist_window (p0 : V × ℝ) {q : ℝ} (hq : 0≤q) (p z : V × ℝ) :
    pdist (window p0 q p) (window p0 q z)=q*pdist p z := by
  simp only [pdist,window,add_sub_add_left_eq_sub,←smul_sub,norm_smul,
    Real.norm_of_nonneg hq,←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hq 4),
    Real.mul_rpow (pow_nonneg hq 4) (abs_nonneg _),pow_four_quarter hq]
  ring
omit [FiniteDimensional ℝ V] in
lemma windowValue_contDiff (p0 : V × ℝ) (q : ℝ) (u : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) : ContDiff ℝ 4 (windowValue p0 q u t) :=
  (hs _).comp (contDiff_const.add (contDiff_const.smul contDiff_id))
omit [FiniteDimensional ℝ V] in
lemma window_jet (p0 : V × ℝ) (q : ℝ) (u : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (n : ℕ) (hn : n≤4) (p : V × ℝ) :
    iteratedFDeriv ℝ n (windowValue p0 q u p.2) p.1=
      q^n • iteratedFDeriv ℝ n (u (window p0 q p).2) (window p0 q p).1 := by
  have hh := iteratedFDeriv_scale q (fun z => u (p0.2+q^4*p.2) (p0.1+z))
    ((hs _).comp (contDiff_const.add contDiff_id)) n hn p.1
  rw [iteratedFDeriv_comp_add_left] at hh
  convert hh using 1 <;> rfl
lemma window_bilaplacian (p0 : V × ℝ) (q : ℝ) (u : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ) :
    Δ (Δ (windowValue p0 q u p.2)) p.1=q^4 • Δ (Δ (u (window p0 q p).2)) (window p0 q p).1 := by
  rw [bilaplacian_eq_traceFour _ (windowValue_contDiff p0 q u hs p.2),window_jet p0 q u hs 4 le_rfl,
    map_smul,bilaplacian_eq_traceFour _ (hs _)]
omit [FiniteDimensional ℝ V] in
lemma window_hasDerivAt (p0 : V × ℝ) (q : ℝ) (u ut : ℝ → V → ℂ) (p : V × ℝ)
    (hd : HasDerivAt (fun t => u t (window p0 q p).1)
      (ut (window p0 q p).2 (window p0 q p).1) (window p0 q p).2) :
    HasDerivAt (fun t => windowValue p0 q u t p.1) (windowTime p0 q ut p.2 p.1) p.2 := by
  have ht := ((hasDerivAt_id p.2).const_mul (q^4)).const_add p0.2
  convert hd.scomp p.2 ht using 1 <;> first | rfl | simp only [windowTime,window,mul_one]
lemma window_equation (p0 : V × ℝ) (q : ℝ) (a : V × ℝ → ℝ) (b : V × ℝ → ℂ)
    (u ut f : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (p : V × ℝ)
    (he : ut (window p0 q p).2 (window p0 q p).1+
      (a (window p0 q p) : ℂ)*Δ (Δ (u (window p0 q p).2)) (window p0 q p).1+
      b (window p0 q p)*u (window p0 q p).2 (window p0 q p).1=f (window p0 q p).2 (window p0 q p).1) :
    windowTime p0 q ut p.2 p.1+(a (window p0 q p) : ℂ)*Δ (Δ (windowValue p0 q u p.2)) p.1+
      (q^4 • b (window p0 q p))*windowValue p0 q u p.2 p.1=windowTime p0 q f p.2 p.1 := by
  rw [window_bilaplacian p0 q u hs p]
  change q^4 • ut (window p0 q p).2 (window p0 q p).1+_+_=q^4 • f (window p0 q p).2 (window p0 q p).1
  rw [←he]
  simp only [Complex.real_smul]
  dsimp only [windowValue,window]
  ring
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma holder_window {α K q : ℝ} (hα : 0≤α) (hq : 0<q) (hq1 : q≤1) (p0 : V × ℝ)
    {Ω S : Set (V × ℝ)} {f : V × ℝ → E}
    (hf : HolderBound α Ω f K) (hm : MapsTo (window p0 q) S Ω) :
    HolderBound α S (fun p => f (window p0 q p)) K := by
  refine ⟨fun p hp => hf.1 _ (hm hp),?_⟩
  intro p hp z hz
  have hh := hf.2 _ (hm hp) _ (hm hz)
  rw [pdist_window p0 hq.le,Real.mul_rpow hq.le (pdist_nonneg p z)] at hh
  have hKa : 0≤K := (norm_nonneg _).trans (hf.1 _ (hm hp))
  apply hh.trans
  have hqa : q^α≤1 := Real.rpow_le_one hq.le hq1 hα
  nlinarith [Real.rpow_nonneg (pdist_nonneg p z) α,mul_nonneg hKa (Real.rpow_nonneg (pdist_nonneg p z) α)]
end ParabolicLocalization

end

end OAI
