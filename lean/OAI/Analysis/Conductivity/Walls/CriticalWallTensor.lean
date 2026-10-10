import Mathlib
import OAI.Analysis.Conductivity.Sobolev.WallParticular
import OAI.Analysis.Conductivity.Geometry.BoxCoordinateBridge
import OAI.Analysis.Conductivity.Variational.MatrixCompact
import OAI.Analysis.Conductivity.Sources.SymmetricCutoffSources

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def wallCoordinatePair (v : Box3 → ℝ) (x : Coord3) : Fin 2 → ℝ :=
  ![x 0,v (boxCoordinates x)]

lemma wallCoordinatePair_smooth {v : Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallCoordinatePair v) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_apply ℝ ℝ (0 : Fin 3)
  · exact hv.comp boxCoordinates.contDiff

lemma wallCoordinatePair_derivative {v : Box3 → ℝ}
    (hv : Differentiable ℝ v) (x w : Coord3) :
    fderiv ℝ (wallCoordinatePair v) x w=![w 0,fderiv ℝ v (boxCoordinates x) (boxCoordinates w)] := by
  have hd : DifferentiableAt ℝ (wallCoordinatePair v) x := by
    apply differentiableAt_pi.mpr
    intro j
    fin_cases j
    · exact differentiableAt_apply (0 : Fin 3) x
    · exact (hv _).comp x boxCoordinates.differentiableAt
  ext j
  fin_cases j
  · have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D w) (fderiv_apply hd (0 : Fin 2))
    change fderiv ℝ (fun x : Coord3 => x 0) x w=fderiv ℝ (wallCoordinatePair v) x w 0 at hh
    have hp : fderiv ℝ (fun x : Coord3 => x 0) x=ContinuousLinearMap.proj (0 : Fin 3) :=
      (ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ).hasFDerivAt.fderiv
    rw [hp] at hh
    exact hh.symm
  · have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D w) (fderiv_apply hd (1 : Fin 2))
    change fderiv ℝ (v∘boxCoordinates) x w=fderiv ℝ (wallCoordinatePair v) x w 1 at hh
    exact hh.symm.trans (boxCoordinates_fderiv v hv x w)

def wallMatrix (A B : Box3 → ℝ) (x : Coord3) : Mat3 :=
  !![0,0,A (boxCoordinates x);0,0,0;A (boxCoordinates x),0,B (boxCoordinates x)]

lemma wallMatrix_symmetric (A B : Box3 → ℝ) (x : Coord3) :
    (wallMatrix A B x).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma wallMatrix_smooth {A B : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallMatrix A B) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  all_goals first | exact contDiff_const | exact hA.comp boxCoordinates.contDiff |
    exact hB.comp boxCoordinates.contDiff

lemma wallMatrix_columns {v : Box3 → ℝ} (hv : Differentiable ℝ v)
    (A B : Box3 → ℝ) (x : Coord3) :
    (wallMatrix A B x*gradientColumns (fderiv ℝ (wallCoordinatePair v) x)).col 0=
      ![0,0,A (boxCoordinates x)] ∧
    (wallMatrix A B x*gradientColumns (fderiv ℝ (wallCoordinatePair v) x)).col 1=
      ![A (boxCoordinates x)*wallDerivative v (boxCoordinates x),0,
        A (boxCoordinates x)*wallAlong (1,0) v (boxCoordinates x)+
        B (boxCoordinates x)*wallDerivative v (boxCoordinates x)] := by
  have he (i : Fin 3) : gradientColumns (fderiv ℝ (wallCoordinatePair v) x) i 0=
      (Pi.single i (1:ℝ) : Coord3) 0 := by
    change fderiv ℝ (wallCoordinatePair v) x (Pi.single i 1) 0=_
    rw [wallCoordinatePair_derivative hv]
    rfl
  have he' (i : Fin 3) : gradientColumns (fderiv ℝ (wallCoordinatePair v) x) i 1=
      fderiv ℝ v (boxCoordinates x) (boxCoordinates (Pi.single i 1)) := by
    change fderiv ℝ (wallCoordinatePair v) x (Pi.single i 1) 1=_
    rw [wallCoordinatePair_derivative hv]
    rfl
  constructor
  · ext i
    change (∑ k,wallMatrix A B x i k*gradientColumns (fderiv ℝ (wallCoordinatePair v) x) k 0)=_
    fin_cases i <;> simp [he,wallMatrix,Pi.single_apply]
  · ext i
    change (∑ k,wallMatrix A B x i k*gradientColumns (fderiv ℝ (wallCoordinatePair v) x) k 1)=_
    fin_cases i <;> simp [Fin.sum_univ_three,he',wallMatrix,
      boxCoordinates_apply,Pi.single_apply,wallDerivative,wallAlong]
    all_goals exact Or.inl rfl

lemma smooth_wall_cutoff_ratio {χ f g : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hne : ∀ p∈tsupport χ,wallQuotient g p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p => χ p*(wallQuotient f p/wallQuotient g p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p∈tsupport χ
  · exact hχ.contDiffAt.mul ((wallQuotient_smooth hf).contDiffAt.div
      (wallQuotient_smooth hg).contDiffAt (hne p hp))
  · apply (show ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (0:ℝ)) p from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    change χ q=0 at hq
    simp only [hq,zero_mul]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wallMatrix_tsupport {A B : Box3 → ℝ} {K : Set Box3}
    (hA : tsupport A⊆K) (hB : tsupport B⊆K) :
    tsupport (wallMatrix A B)⊆boxCoordinates ⁻¹' K := by
  apply matrix_tsupport_subset (wallMatrix A B)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (tsupport_comp_subset_preimage A boxCoordinates.continuous).trans (preimage_mono hA)
    | exact (tsupport_comp_subset_preimage B boxCoordinates.continuous).trans (preimage_mono hB)
    | simp [wallMatrix]

lemma wallMatrix_compact {A B : Box3 → ℝ}
    (hA : HasCompactSupport A) (hB : HasCompactSupport B) :
    HasCompactSupport (wallMatrix A B) := by
  apply matrix_hasCompactSupport (wallMatrix A B)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hA.comp_homeomorph boxCoordinates.toHomeomorph
    | exact hB.comp_homeomorph boxCoordinates.toHomeomorph
    | exact HasCompactSupport.zero

lemma coordinateDivergence_wallFlux {f g : Box3 → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Coord3) :
    coordinateDivergence (fun y => ![f (boxCoordinates y),0,g (boxCoordinates y)]) x=
      wallAlong (1,0) f (boxCoordinates x)+wallDerivative g (boxCoordinates x) := by
  have he : coordinateDivergence (fun y => ![f (boxCoordinates y),0,g (boxCoordinates y)]) x=
      fderiv ℝ (f∘boxCoordinates) x (Pi.single 0 1)+
      fderiv ℝ (g∘boxCoordinates) x (Pi.single 2 1) := by
    simp [coordinateDivergence,Fin.sum_univ_three,Function.comp_def]
  rw [he,boxCoordinates_fderiv f hf,boxCoordinates_fderiv g hg]
  rfl

lemma wallMatrix_sources {A B v : Box3 → ℝ}
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (x : Coord3) :
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=wallDerivative A (boxCoordinates x) ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=
      wallAlong (1,0) (fun p => A p*wallDerivative v p) (boxCoordinates x)+
        wallDerivative (fun p => A p*wallAlong (1,0) v p+B p*wallDerivative v p) (boxCoordinates x) := by
  have he₀ : (fun y => (wallMatrix A B y*gradientColumns (fderiv ℝ (wallCoordinatePair v) y)).col 0)=
      (fun y => ![0,0,A (boxCoordinates y)]) := funext (fun y => (wallMatrix_columns (hv.differentiable (by simp)) A B y).1)
  have he₁ : (fun y => (wallMatrix A B y*gradientColumns (fderiv ℝ (wallCoordinatePair v) y)).col 1)=
      (fun y => ![A (boxCoordinates y)*wallDerivative v (boxCoordinates y),0,
        A (boxCoordinates y)*wallAlong (1,0) v (boxCoordinates y)+B (boxCoordinates y)*wallDerivative v (boxCoordinates y)]) :=
    funext (fun y => (wallMatrix_columns (hv.differentiable (by simp)) A B y).2)
  constructor
  · unfold symmetricSource
    rw [he₀,coordinateDivergence_wallFlux (differentiable_const 0) (hA.differentiable (by simp))]
    simp [wallAlong]
  · unfold symmetricSource
    rw [he₁]
    exact coordinateDivergence_wallFlux
      ((hA.mul (wallDerivative_smooth hv)).differentiable (by simp))
      (((hA.mul (wallAlong_smooth (1,0) hv)).add (hB.mul (wallDerivative_smooth hv))).differentiable (by simp)) x

def wallParticularTensor (χ v r₁ r₂ : Box3 → ℝ) : Coord3 → Mat3 :=
  wallMatrix (fun p => χ p*wallPrimitive r₁ p)
    (fun p => χ p*(wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) p/wallQuotient (wallDerivative v) p))

lemma wallParticularTensor_smooth {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallParticularTensor χ v r₁ r₂) :=
  wallMatrix_smooth (hχ.mul (wallPrimitive_smooth h₁))
    (smooth_wall_cutoff_ratio hχ (wallParticularNumerator_smooth (1,0) hv h₁ h₂)
      (wallDerivative_smooth hv) hne)

lemma wallParticularTensor_compact {χ v r₁ r₂ : Box3 → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (wallParticularTensor χ v r₁ r₂) ∧
      tsupport (wallParticularTensor χ v r₁ r₂)⊆boxCoordinates ⁻¹' tsupport χ :=
  ⟨wallMatrix_compact hs.mul_right hs.mul_right,
    wallMatrix_tsupport tsupport_mul_subset_left tsupport_mul_subset_left⟩

theorem wallParticularTensor_source_eq {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (x : Coord3) (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) :
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 0 x=r₁ (boxCoordinates x) ∧
    symmetricSource (wallParticularTensor χ v r₁ r₂) (wallCoordinatePair v) 1 x=r₂ (boxCoordinates x) := by
  let p := boxCoordinates x
  let A := fun q => χ q*wallPrimitive r₁ q
  let B := fun q => χ q*(wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) q/wallQuotient (wallDerivative v) q)
  have hA := hχ.mul (wallPrimitive_smooth h₁)
  have hB := smooth_wall_cutoff_ratio hχ (wallParticularNumerator_smooth (1,0) hv h₁ h₂) (wallDerivative_smooth hv) hne
  have hxe : χ p=1 := hx.eq_of_nhds
  have hp : p∈tsupport χ := subset_tsupport χ (by change χ p≠0; rw [hxe]; norm_num)
  have hqn : ∀ᶠ q in 𝓝 p,wallQuotient (wallDerivative v) q≠0 :=
    (wallQuotient_smooth (wallDerivative_smooth hv)).continuous.continuousAt.eventually_ne (hne p hp)
  have hAe : A =ᶠ[𝓝 p] wallPrimitive r₁ := hx.mono (fun q hq => by dsimp [A]; rw [hq,one_mul])
  have hFe : (fun q => A q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => wallPrimitive r₁ q*wallDerivative v q) := hAe.mono (fun q hq => by dsimp only; rw [hq])
  have hGe : (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => wallPrimitive r₁ q*wallAlong (1,0) v q+wallParticularNumerator (1,0) v r₁ r₂ q) := by
    filter_upwards [hx,hqn] with q hq hqn
    dsimp [A,B]
    rw [hq,one_mul,one_mul,wall_ratio_multiply (wallParticularNumerator_smooth (1,0) hv h₁ h₂)
      (wallDerivative_smooth hv) (wallParticularNumerator_zero (1,0) v r₁ r₂) hz q hqn]
  have hsource := wallMatrix_sources hA hB hv x
  change symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=_ ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=_
  rw [hsource.1,hsource.2]
  change wallDerivative A p=r₁ p ∧ _=r₂ p
  refine ⟨?_,?_⟩
  · change fderiv ℝ A p (0,1)=r₁ p
    rw [hAe.fderiv_eq]
    exact wallDerivative_primitive h₁ p
  · change fderiv ℝ (fun q => A q*wallDerivative v q) p ((1,0),0)+
      fderiv ℝ (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p (0,1)=r₂ p
    rw [hFe.fderiv_eq,hGe.fderiv_eq]
    exact (wall_particular_flux_equations (1,0) hv h₁ h₂ p).2

theorem wallParticularTensor_weak_moments {χ v r₁ r₂ : Box3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    let H := wallParticularTensor χ v r₁ r₂
    let u := wallCoordinatePair v
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j)) ∧
    (∀ j,HasCompactSupport (symmetricSource H u j)) ∧
    (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x)) ∧
    (∫ x,symmetricSource H u 0 x)=0 ∧ (∫ x,symmetricSource H u 1 x)=0 ∧
    (∫ x,u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)=0 :=
  symmetric_cutoff_sources _ (wallParticularTensor_smooth hχ hv h₁ h₂ hne)
    (wallParticularTensor_compact hs).1 (wallMatrix_symmetric _ _) _ (wallCoordinatePair_smooth hv)

end ScalarConductivity

end

end OAI
