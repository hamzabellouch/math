import OAI.Analysis.AncientFlat.Evolution.InitialCore
import OAI.Analysis.AncientFlat.Evolution.SourceEvolution
import OAI.Analysis.AncientFlat.Regularity.ConstantSchauder
import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParabolicInitial
open ParabolicInterior ParabolicSchauder ParametrixEvolution ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem exists_initial_model (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (g : C₀(V,ℂ)) (F : ℝ), 0≤F → ‖g‖≤F →
      (∀ x y, ‖g x-g y‖≤F*‖x-y‖^α) →
      ∃ u : ℝ → C₀(V,ℂ), u 0=0 ∧
        (∀ t∈Icc 0 (1/2:ℝ), ContDiff ℝ 4 (fun x => u t x)) ∧
        HolderBound α {p : V × ℝ | p.2∈Icc 0 (1/2:ℝ)}
          (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) (C*F) ∧
        (∀ t∈Icc 0 (1/2:ℝ), ∀ x, HasDerivWithinAt (fun s => u s x)
          (g x-Δ (Δ (fun y => u t y)) x) (Icc 0 (1/2:ℝ)) t) ∧
        (∀ t∈Icc 0 (1/2:ℝ), ∀ x, ‖u t x‖≤C*F) ∧
        (∀ t∈Icc 0 (1/2:ℝ), ∀ x, ‖g x-Δ (Δ (fun y => u t y)) x‖≤C*F) := by
  obtain ⟨C,hC,H⟩ := constant_fourth_estimate (V := V) α hα hα1
  let L := (traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)
  let D := 1+C+‖L‖*C
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro g F hF hg hh
  let f : ℝ →ᵇ C₀(V,ℂ) := BoundedContinuousFunction.const ℝ g
  have hf : ∃ H : ℝ, 0≤H ∧ ∀ t∈Icc 0 (1:ℝ), ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^α :=
    ⟨F,hF,fun _ _ => hh⟩
  have hb : ∀ s∈Icc 0 (1:ℝ), ‖(0 : C(ℝ,V →ᵇ ℂ)) s‖≤0 := by simp
  have hLip : ∀ s∈Icc 0 (1:ℝ), ∀ r∈Icc 0 (1:ℝ), ∀ x z : V,
      |((unitLine (V := V)) s x).val-(unitLine r z).val|≤0*(‖x-z‖+|s-r|) := by
    intros; simp [unitLine,unitCoefficient]
  have hLipb : ∀ s∈Icc 0 (1:ℝ), ∀ x z : V,
      ‖(0 : C(ℝ,V →ᵇ ℂ)) s x-(0 : C(ℝ,V →ᵇ ℂ)) s z‖≤0*‖x-z‖ := by simp
  have hA : ∀ s∈Icc 0 (1:ℝ), ContDiff ℝ ∞ (fun x : V => ((unitLine (V := V)) s x).val) :=
    fun _ _ => contDiff_const
  obtain ⟨u,hu⟩ := exists_source_evolves zero_lt_one 0 0 le_rfl le_rfl unitLine 0
    1 zero_le_one le_rfl hb hLip hLipb hA α hα hα1.le f hf 0
  have HT := H 1 zero_lt_one le_rfl f F hF (fun _ _ => hh) u hu
  have hsub : Icc (0:ℝ) (1/2)⊆Icc 0 1 := fun _ ht => ⟨ht.1,by linarith [ht.2]⟩
  have hs (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) : ContDiff ℝ 4 (fun x => u t x) := by
    by_cases ht0 : t=0
    · subst t; simp only [hu.1,ZeroAtInftyContinuousMap.zero_apply]; exact contDiff_const
    · exact hu.2.2.1 t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩
  have hi := hu.initial_derivative zero_lt_one 1 0 0 zero_le_one le_rfl le_rfl
    unitLine 0 1 zero_lt_one le_rfl hb hLip hLipb hA
    (fun _ _ n _ x => unitLine_jets n x) α hα hα1.le f hf
  have hzero (x : V) : Δ (Δ (fun y => u 0 y)) x=0 := by
    rw [bilaplacian_eq_traceFour _ (hs 0 ⟨le_rfl,by norm_num⟩)]
    simp [hu.1]
  have hd (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) (x : V) : HasDerivWithinAt (fun s => u s x)
      (g x-Δ (Δ (fun y => u t y)) x) (Icc 0 (1/2:ℝ)) t := by
    by_cases ht0 : t=0
    · subst t
      rw [hzero,sub_zero,hasDerivWithinAt_iff_tendsto_slope]
      have hx := ((C0Convolution.eval x).continuous.tendsto (g)).comp hi
      have hm : Icc (0:ℝ) (1/2)\{0}⊆Ioi 0 := by
        intro s hs
        exact lt_of_le_of_ne hs.1.1 (Ne.symm (by simpa using hs.2))
      apply (hx.mono_left (nhdsWithin_mono 0 hm)).congr
      intro s
      simp [slope,hu.1,C0Convolution.eval_apply]
    · obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩
      have hh := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t hp
      have he : p x=g x-Δ (Δ (fun y => u t y)) x := by
        simpa [f,unitLine,unitCoefficient] using hpe x
      simpa only [Function.comp_def,BoundedContinuousFunction.evalCLM_apply,
        ZeroAtInftyContinuousMap.toBCF_apply,he] using hh.hasDerivWithinAt (s := Icc 0 (1/2:ℝ))
  have htop : HolderBound α {p : V × ℝ | p.2∈Icc 0 (1/2:ℝ)}
      (fun p => iteratedFDeriv ℝ 4 (fun x => u p.2 x) p.1) (D*F) :=
    (HT.restrict (fun _ ht => hsub ht)).mono (mul_le_mul_of_nonneg_right (by dsimp [D]; nlinarith [mul_nonneg (norm_nonneg L) hC.le]) hF)
  have hv (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) (x : V) :
      ‖g x-Δ (Δ (fun y => u t y)) x‖≤D*F := by
    have htrace : ‖Δ (Δ (fun y => u t y)) x‖≤‖L‖*(C*F) := by
      rw [bilaplacian_eq_traceFour _ (hs t ht)]
      exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (HT.1 (x,t) (hsub ht)) (norm_nonneg L))
    have hgx : ‖g x‖≤F := (g.toBCF.norm_coe_le_norm x).trans hg
    apply (norm_sub_le _ _).trans
    dsimp [D]
    nlinarith
  have hvu (t : ℝ) (ht : t∈Icc 0 (1/2:ℝ)) (x : V) : ‖u t x‖≤D*F := by
    have he := (convex_Icc (0:ℝ) (1/2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => hd s hs x) (fun s hs => hv s hs x) (show (0:ℝ)∈Icc 0 (1/2:ℝ) from ⟨le_rfl,by norm_num⟩) ht
    simp only [hu.1,ZeroAtInftyContinuousMap.zero_apply,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at he
    exact he.trans (mul_le_of_le_one_right (mul_nonneg hD.le hF) (by linarith [ht.2]))
  exact ⟨u,hu.1,hs,htop,hd,hvu,hv⟩
end ParabolicInitial

end

end OAI
