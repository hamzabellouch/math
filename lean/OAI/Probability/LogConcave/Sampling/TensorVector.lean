import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ArrayComponentPolySmooth
import OAI.Probability.LogConcave.Analysis.ProductPotentialMeasurable
import OAI.Probability.LogConcave.Sampling.IterTensorLie

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma lie_chain {S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) (c : S → Fin d) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => iterTensorLie H A F n c (γ u))
      (iterTensorLie H A F (n+1) c (γ t)) s t := by
  have hf := (iterTensorLie_polySmooth hH A F hA hF n c).smooth.differentiable (by simp)
  have hd := (hf (γ t)).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  change HasDerivWithinAt ((iterTensorLie H A F n c) ∘ γ)
    (tensorLie H A (iterTensorLie H A F n) c (γ t)) s t
  rw [tensorLie_eq_directional H A (iterTensorLie H A F n)
    (fun c => (hA c).smooth) (fun c => (iterTensorLie_polySmooth hH A F hA hF n c).smooth)
    hsk c (γ t)]
  exact hd

def tensorVector {S : Type} {d : ℕ} (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    EuclideanSpace ℝ (S → Fin d) := WithLp.toLp 2 (fun c => F c y)

lemma tensorVector_norm_sq {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (y : Point d) :
    ‖tensorVector F y‖^2=∑c,(F c y)^2 := EuclideanSpace.real_norm_sq_eq _

lemma tensorVector_contDiff {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) :
    ContDiff ℝ (⊤:ℕ∞) (tensorVector F) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr hF)

lemma lie_vector_chain {S : Type} [Fintype S] {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (F : (S → Fin d) → Point d → ℝ) (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    {s : Set ℝ} (γ : ℝ → Point d)
    (hγ : ∀t∈s,HasDerivWithinAt γ (skewLieField H A (γ t)) s t)
    (n : ℕ) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (fun u => tensorVector (iterTensorLie H A F n) (γ u))
      (tensorVector (iterTensorLie H A F (n+1)) (γ t)) s t := by
  have h := hasDerivWithinAt_pi.mpr (fun c => lie_chain hH A F hA hF hsk γ hγ n c ht)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S → Fin d => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t h
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def leftCoordinates (d e : ℕ) : Fin d ↪ Fin (d+e) := ⟨Fin.castAdd e,Fin.castAdd_injective d e⟩
def rightCoordinates (d e : ℕ) : Fin e ↪ Fin (d+e) := ⟨Fin.natAdd d,Fin.natAdd_injective e d⟩

lemma coordinateProjection_left {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (leftCoordinates d e) y=(productPointEquiv d e y).1 := by
  ext i
  rfl
lemma coordinateProjection_right {d e : ℕ} (y : Point (d+e)) :
    coordinateProjection (rightCoordinates d e) y=(productPointEquiv d e y).2 := by
  ext i
  rfl

lemma productPointEquiv_basis_left {d e : ℕ} (i : Fin d) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))=
      (EuclideanSpace.basisFun (Fin d) ℝ i,0) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    exact coordinateProjection_basis_in (leftCoordinates d e) i
  · rw [←coordinateProjection_right]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [rightCoordinates] at hh
    omega
lemma productPointEquiv_basis_right {d e : ℕ} (i : Fin e) :
    productPointEquiv d e (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))=
      (0,EuclideanSpace.basisFun (Fin e) ℝ i) := by
  apply Prod.ext
  · rw [←coordinateProjection_left]
    apply coordinateProjection_basis_out
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    dsimp [leftCoordinates] at hh
    omega
  · rw [←coordinateProjection_right]
    exact coordinateProjection_basis_in (rightCoordinates d e) i

lemma directional_comp_linear {d e : ℕ} {f : Point e → ℝ}
    (hf : Differentiable ℝ f) (L : Point d →L[ℝ] Point e) (v y : Point d) :
    directional v (fun z => f (L z)) y=directional (L v) f (L y) := by
  exact congrArg (fun A : Point d →L[ℝ] ℝ => A v)
    ((hf (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv

lemma productPotential_directional_left {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin d) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.castAdd e))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin d) ℝ i) H (productPointEquiv d e y).1 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_left (e:=e) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,L,coordinateProjection_left]

lemma productPotential_directional_right {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) (i : Fin e) (y : Point (d+e)) :
    directional (EuclideanSpace.basisFun (Fin (d+e)) ℝ (i.natAdd d))
      (productPotential H G) y=
      directional (EuclideanSpace.basisFun (Fin e) ℝ i) G (productPointEquiv d e y).2 := by
  let L := coordinateProjection (leftCoordinates d e)
  let R := coordinateProjection (rightCoordinates d e)
  have he : productPotential H G=(fun z => H (L z)+G (R z)) := by
    funext z; simp [productPotential,L,R,coordinateProjection_left,coordinateProjection_right]
  rw [he,directional_add (f:=fun z => H (L z)) (g:=fun z => G (R z))
    (hH.comp L.differentiable) (hG.comp R.differentiable)]
  dsimp only
  rw [directional_comp_linear hH L,directional_comp_linear hG R]
  have hb := productPointEquiv_basis_right (d:=d) i
  have hbL := congrArg Prod.fst hb
  have hbR := congrArg Prod.snd hb
  rw [←coordinateProjection_left] at hbL
  rw [←coordinateProjection_right] at hbR
  change L _=_ at hbL
  change R _=_ at hbR
  rw [hbL,hbR]
  simp [directional,R,coordinateProjection_right]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators
open TensorEnergy

lemma spatialEnergy_leftLift {S : Type} [Fintype S] {d e : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) [SFinite (gibbs H)] (F : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (ι : S → Fin d ↪ Fin (d+e)) (j : ℕ) :
    spatialEnergy (arrayCoordinateLift (leftCoordinates d e) ι F) j
      (gibbs (productPotential H (fun y : Point e => ‖y‖^2/2)))=spatialEnergy F j (gibbs H) := by
  let E := productPointEquiv d e
  have hmeas : AEStronglyMeasurable (fun p : Point d × Point e => spatialSquared F j p.1)
      ((gibbs (productPotential H (fun y : Point e => ‖y‖^2/2))).map E) := by
    apply Continuous.aestronglyMeasurable
    unfold spatialSquared squared
    exact continuous_finsetSum _ (fun _ _ =>
      ((JetCalculus.smooth_jet (hF _) _ _).continuous.comp continuous_fst).pow 2)
  unfold spatialEnergy
  simp_rw [spatialSquared_coordinateLift _ _ _ hF,coordinateProjection_left]
  rw [←integral_map E.continuous.measurable.aemeasurable hmeas,
    productPotential_gibbs hH (gaussianPotential_polySmooth e).smooth.continuous,gaussianPotential_gibbs]
  rw [integral_fun_fst]
  simp
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def jointSkewEntry {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (i z : Fin (d+d)) (y : Point (d+d)) : ℝ :=
  s⁻¹ * Fin.addCases
    (fun a => Fin.addCases (fun _ => 0) (fun b =>
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ b)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ a))) z)
    (fun a => Fin.addCases (fun b =>
      -inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ a)
        (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ b))) (fun _ => 0) z) i

def jointSkew {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (c : Unit ⊕ Unit → Fin (d+d)) : Point (d+d) → ℝ :=
  jointSkewEntry K s (c (.inl ())) (c (.inr ()))

lemma jointSkew_skew {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ)
    (i z : Fin (d+d)) (y : Point (d+d)) :
    jointSkew K s (Sum.elim (fun _ => i) (fun _ => z)) y=
      -jointSkew K s (Sum.elim (fun _ => z) (fun _ => i)) y := by
  induction i using Fin.addCases <;> induction z using Fin.addCases <;>
    simp only [jointSkew,jointSkewEntry,Sum.elim_inl,Sum.elim_inr,Fin.addCases_left,Fin.addCases_right,mul_zero,mul_neg,neg_neg,neg_zero]

lemma jointSkew_polySmooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀i j,PolySmooth (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j)))) (s : ℝ) (c : Unit ⊕ Unit → Fin (d+d)) :
    PolySmooth (jointSkew K s c) := by
  suffices h : ∀i z : Fin (d+d),PolySmooth (jointSkewEntry K s i z) from h _ _
  intro i z
  let L := (ContinuousLinearMap.fst ℝ (Point d) (Point d)).comp
    (productPointEquiv d d).toContinuousLinearMap
  have hL (y : Point (d+d)) : L y=(productPointEquiv d d y).1 := rfl
  change PolySmooth (fun y => jointSkewEntry K s i z y)
  induction i using Fin.addCases <;> induction z using Fin.addCases
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul ((hK _ _).comp_linear L)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,hL] using (PolySmooth.const s⁻¹).mul (((hK _ _).comp_linear L).neg)
  · simpa only [jointSkewEntry,Fin.addCases_left,Fin.addCases_right,mul_zero] using (PolySmooth.const (0:ℝ) : PolySmooth (fun _ : Point (d+d) => 0))

lemma skewLieField_coordinate {D : ℕ} (H : Point D → ℝ)
    (A : (Unit ⊕ Unit → Fin D) → Point D → ℝ) (y : Point D) (z : Fin D) :
    skewLieField H A y z=∑i : Fin D,adjointCoordinate H (EuclideanSpace.basisFun (Fin D) ℝ i)
      (A (Sum.elim (fun _ => i) (fun _ => z))) y := by
  simp [skewLieField,EuclideanSpace.basisFun_apply,Pi.single_apply]

lemma directional_gaussianPotential {d : ℕ} (v y : Point d) :
    directional v (fun z : Point d => ‖z‖^2/2) y=inner ℝ y v := by
  have hd := ((hasFDerivAt_id y).norm_sq.const_mul (1/2 : ℝ)).fderiv
  change (fderiv ℝ (fun z : Point d => ‖z‖^2/2) y) v=_
  have he : (fun z : Point d => ‖z‖^2/2)=(fun z : Point d => (1/2:ℝ)*‖z‖^2) := by funext z; ring
  dsimp only [id_eq] at hd
  rw [he,hd]
  simp

lemma adjointCoordinate_const_mul {d : ℕ} {H f : Point d → ℝ}
    (hf : Differentiable ℝ f) (v : Point d) (c : ℝ) :
    adjointCoordinate H v (fun y => c*f y)=fun y => c*adjointCoordinate H v f y := by
  unfold adjointCoordinate
  rw [directional_mul (differentiable_const c) hf]
  funext y
  simp only [directional,fderiv_fun_const]
  change -(0*f y+c*(fderiv ℝ f y) v)+(fderiv ℝ H y) v*(c*f y)=_
  ring

lemma adjointCoordinate_zero {d : ℕ} (H : Point d → ℝ) (v : Point d) :
    adjointCoordinate H v (fun _ => 0)=fun _ => 0 := by
  funext y
  simp [adjointCoordinate,directional]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

def pairLabels {D : ℕ} (i j : Fin D) : Unit ⊕ Unit → Fin D := Sum.elim (fun _ => i) (fun _ => j)

lemma eq_pairLabels {D : ℕ} (c : Unit ⊕ Unit → Fin D) : c=pairLabels (c (.inl ())) (c (.inr ())) := by
  funext a
  rcases a with ⟨⟩|⟨⟩ <;> rfl

lemma pair_lift_in {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin d) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F
      (pairLabels (e₁ i) (e₂ j)) y=F (pairLabels i j) (coordinateProjection e y) := by
  have he : pairLabels (e₁ i) (e₂ j)=slotEmbedding (Sum.elim (fun _ => e₁) (fun _ => e₂)) (pairLabels i j) := by
    funext a; rcases a with ⟨⟩|⟨⟩ <;> rfl
  rw [he]
  exact zeroExtend_apply _ _ _

lemma pair_lift_out_left {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hi ⟨c (.inl ()),congrFun hc (.inl ())⟩
lemma pair_lift_out_right {d D : ℕ} (e e₁ e₂ : Fin d ↪ Fin D)
    (F : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (i j : Fin D) (hj : j∉Set.range e₂) (y : Point D) :
    arrayCoordinateLift e (Sum.elim (fun _ => e₁) (fun _ => e₂)) F (pairLabels i j) y=0 := by
  apply zeroExtend_out
  rintro ⟨c,hc⟩
  exact hj ⟨c (.inr ()),congrFun hc (.inr ())⟩

lemma left_not_right {d e : ℕ} (i : Fin d) : i.castAdd e∉Set.range (rightCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [rightCoordinates] at hh
  omega
lemma right_not_left {d e : ℕ} (i : Fin e) : i.natAdd d∉Set.range (leftCoordinates d e) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  dsimp [leftCoordinates] at hh
  omega

lemma jointSkew_eq_lifts {d : ℕ} (K : Point d → Point d →L[ℝ] Point d) (s : ℝ) :
    jointSkew K s=fun c y =>
      s⁻¹*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d))
        (fun c y => matrixArray d (K y) (c ∘ Equiv.sumComm Unit Unit)) c y+
      (-s⁻¹)*arrayCoordinateLift (leftCoordinates d d)
        (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d))
        (fun c y => matrixArray d (K y) c) c y := by
  funext c y
  rw [eq_pairLabels c]
  generalize c (.inl ())=i,c (.inr ())=j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rw [pair_lift_out_right _ _ _ _ _ _ (left_not_right _),
      pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,mul_zero,add_zero]
  · change _=s⁻¹*arrayCoordinateLift _ _ _
      (pairLabels (leftCoordinates d d _) (rightCoordinates d d _)) y+_
    rw [pair_lift_in,pair_lift_out_left _ _ _ _ _ _ (left_not_right _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,add_zero,coordinateProjection_left]
    rfl
  · change _=_+(-s⁻¹)*arrayCoordinateLift _ _ _
      (pairLabels (rightCoordinates d d _) (leftCoordinates d d _)) y
    rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),pair_lift_in]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_left,
      Fin.addCases_right,mul_zero,zero_add,coordinateProjection_left,mul_neg,neg_mul]
    rfl
  · rw [pair_lift_out_left _ _ _ _ _ _ (right_not_left _),
      pair_lift_out_right _ _ _ _ _ _ (right_not_left _)]
    simp only [jointSkew,pairLabels,Sum.elim_inl,Sum.elim_inr,jointSkewEntry,Fin.addCases_right,mul_zero,add_zero]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

lemma spatialTensor_add {S J : Type} {d : ℕ}
    (F G : (S → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c)) (l : List J) (y : Point d) :
    spatialTensor (fun c z => F c z+G c z) l y=
      fun c => spatialTensor F l y c+spatialTensor G l y c := by
  funext c
  exact congrFun (JetCalculus.jet_add (hF _) (hG _) _ l) y

theorem jointSkew_spatial_bound {d n : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    (hK : ∀c,ContDiff ℝ (⊤:ℕ∞) (fun y => matrixArray d (K y) c))
    {M : ℝ} (hM : 0≤M)
    (hb : ∀y,AllSplitBound (spatialTensor (fun c z => matrixArray d (K z) c) (List.finRange n) y) M)
    (s : ℝ) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (jointSkew K s) (List.finRange n) y) (2*|s⁻¹| *M) := by
  let F := fun c z => matrixArray d (K z) c
  let G := fun c => F (c ∘ Equiv.sumComm Unit Unit)
  have hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c) := fun _ => hK _
  have hbg (z : Point d) : AllSplitBound (spatialTensor G (List.finRange n) z) M := by
    apply spatialTensor_allSplit_relabel F hK (Equiv.sumComm Unit Unit) (Equiv.refl (Fin n))
      (List.finRange n) (List.finRange n) _ z M (hb z)
    simp
  let L := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => leftCoordinates d d) (fun _ => rightCoordinates d d)) G
  let R := arrayCoordinateLift (leftCoordinates d d)
    (Sum.elim (fun _ => rightCoordinates d d) (fun _ => leftCoordinates d d)) F
  have hL : ∀c,ContDiff ℝ (⊤:ℕ∞) (L c) := arrayCoordinateLift_smooth _ _ _ hG
  have hR : ∀c,ContDiff ℝ (⊤:ℕ∞) (R c) := arrayCoordinateLift_smooth _ _ _ hK
  have hbL : AllSplitBound (spatialTensor L (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hG hbg y
  have hbR : AllSplitBound (spatialTensor R (List.finRange n) y) M :=
    AllSplitBound.coordinateLift _ _ _ hK hb y
  have he : jointSkew K s=fun c z => s⁻¹*L c z+(-s⁻¹)*R c z := jointSkew_eq_lifts K s
  rw [he,spatialTensor_add _ _ (fun c => contDiff_const.mul (hL c))
    (fun c => contDiff_const.mul (hR c)),spatialTensor_const_mul L hL,
    spatialTensor_const_mul R hR]
  have hh := (hbL.abs_const_mul s⁻¹).add (hbR.abs_const_mul (-s⁻¹))
    (mul_nonneg (abs_nonneg _) hM) (mul_nonneg (abs_nonneg _) hM)
  convert hh using 1
  rw [abs_neg]
  ring

theorem centering_jointSkew_spatial_bound {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (s : ℝ) (y : Point (d+d)) :
    AllSplitBound (spatialTensor (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
      (List.finRange n) y) (2*|s⁻¹| *(((lam:ℝ)*r)*kernelMajorant n/R^n)) := by
  apply jointSkew_spatial_bound
    (fun c => (centeringKernel_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)
    (div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _))
  intro z
  exact spatialTensor_finRange_of_arrayBound
    ((matrixArray d).contDiff.comp (centeringKernel_smooth hF x hr hlam hl hT0 hT1)) z
    (centeringKernel_iterated_split (n:=n) hF x hr hlam hl hR hRT hT0 hT1 z)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators
open TensorEnergy

lemma scoreLabels_eq {d : ℕ} (c : Empty ⊕ Unit → Fin d) :
    c=fun _ => c (.inr ()) := by
  funext a
  rcases a with e|⟨⟩
  · exact e.elim
  · rfl

lemma scalarSlot_lift_in {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin d) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => e₁ i) y=
      F (fun _ => i) (coordinateProjection e y) := by
  exact zeroExtend_apply (slotEmbedding (fun _ : Empty ⊕ Unit => e₁))
    (fun a => F a (coordinateProjection e y)) (fun _ => i)

lemma scalarSlot_lift_out {d D : ℕ} (e e₁ : Fin d ↪ Fin D)
    (F : (Empty ⊕ Unit → Fin d) → Point d → ℝ) (i : Fin D) (hi : i∉Set.range e₁) (y : Point D) :
    arrayCoordinateLift e (fun _ => e₁) F (fun _ => i) y=0 := by
  apply zeroExtend_out
  rintro ⟨a,ha⟩
  exact hi ⟨a (.inr ()),congrFun ha (.inr ())⟩

lemma scoreField_product {d e : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : Differentiable ℝ H) (hG : Differentiable ℝ G) :
    scoreField (productPotential H G)=fun c y =>
      arrayCoordinateLift (leftCoordinates d e) (fun _ => leftCoordinates d e) (scoreField H) c y+
      arrayCoordinateLift (rightCoordinates d e) (fun _ => rightCoordinates d e) (scoreField G) c y := by
  funext c y
  rw [scoreLabels_eq c]
  generalize c (.inr ())=i
  induction i using Fin.addCases with
  | left i =>
    change _=arrayCoordinateLift _ _ _ (fun _ => leftCoordinates d e i) y+_
    rw [scalarSlot_lift_in,scalarSlot_lift_out _ _ _ _ (left_not_right i),add_zero,coordinateProjection_left]
    exact productPotential_directional_left hH hG i y
  | right i =>
    change _=_+arrayCoordinateLift _ _ _ (fun _ => rightCoordinates d e i) y
    rw [scalarSlot_lift_out _ _ _ _ (right_not_left i),scalarSlot_lift_in,zero_add,coordinateProjection_right]
    exact productPotential_directional_right hH hG i y

lemma scoreField_product_allSplit {d e n : ℕ} {H : Point d → ℝ} {G : Point e → ℝ}
    (hH : PolySmooth H) (hG : PolySmooth G) {M N : ℝ} (hM : 0≤M) (hN : 0≤N)
    (hbH : ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange n) y) M)
    (hbG : ∀y,AllSplitBound (spatialTensor (scoreField G) (List.finRange n) y) N)
    (y : Point (d+e)) :
    AllSplitBound (spatialTensor (scoreField (productPotential H G)) (List.finRange n) y) (M+N) := by
  have hsH (c) := (scoreField_polySmooth hH c).smooth
  have hsG (c) := (scoreField_polySmooth hG c).smooth
  rw [scoreField_product (hH.smooth.differentiable (by simp)) (hG.smooth.differentiable (by simp)),
    spatialTensor_add _ _ (arrayCoordinateLift_smooth _ _ _ hsH) (arrayCoordinateLift_smooth _ _ _ hsG)]
  exact (AllSplitBound.coordinateLift _ _ _ hsH hbH y).add
    (AllSplitBound.coordinateLift _ _ _ hsG hbG y) hM hN
end LogConcaveSampling

end

end

end

end OAI
