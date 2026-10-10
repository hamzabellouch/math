import Mathlib
import OAI.Probability.LogConcave.JetEstimates.SpaceBasis

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma tensorAdjoint_scalar {d : ℕ} {ι : Type*} [Fintype ι]
    (H : Point d → ℝ) (b : ι → Point d) {V : ι → Point d → ℝ}
    (hV : ∀i,Differentiable ℝ (V i)) (c : ℝ) :
    tensorAdjoint H b (fun i y => c*V i y)=fun y => c*tensorAdjoint H b V y := by
  unfold tensorAdjoint adjointCoordinate
  change (fun y => ∑i, (-JetCalculus.dir (b i) (fun z => c*V i z) y+
    directional (b i) H y*(c*V i y)))=_
  simp_rw [JetCalculus.dir_const_mul (hV _)]
  funext y
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change -(c*JetCalculus.dir (b i) (V i) y)+directional (b i) H y*(c*V i y)=
    c*(-JetCalculus.dir (b i) (V i) y+directional (b i) H y*V i y)
  ring

lemma conditionalU_one_eq_dir {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (u v : Point d) :
    (fun y => conditionalU F x r ρ y u ((lam:ℝ)*r) (fun _ : Unit => v) [()])=
      fun y => ρ⁻¹*JetCalculus.dir v (fun z => inner ℝ u (conditionalFieldMean F x r ρ z)) y := by
  funext y
  have hh := conditionalFieldMean_jet_U hF x hr hlam hl hρ0.le hρ1 u y
    (fun _ : Unit => v) [()]
  have hm : conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))=
      fun y => inner ℝ u (conditionalFieldMean F x r ρ y) :=
    (funext (conditionalFieldMean_inner hF x hr.le hl hρ0.le hρ1 u)).symm
  rw [hm] at hh
  simp only [JetCalculus.jet,List.length_singleton,pow_one] at hh
  rw [hh]
  field_simp [hρ0.ne']

lemma material_score_algebra {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (u y : Point d) :
    materialScalar F x r (fun t z => inner ℝ u z+r*t*inner ℝ u (conditionalFieldMean F x r t z)) ρ y=
      r*ρ*materialScalar F x r (fun t z => inner ℝ u (conditionalFieldMean F x r t z)) ρ y := by
  let m := fun t z => inner ℝ u (conditionalFieldMean F x r t z)
  have hsq : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have hj : DifferentiableAt ℝ (fun p : ℝ × Point d => m p.1 p.2) (ρ,y) :=
    ((innerSL ℝ u).contDiff.contDiffAt.comp (ρ,y)
    (conditionalFieldMean_joint_smooth hF x hr (by linarith) (ρ,y) hsq)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ (fun t : ℝ => (t,y)) ρ :=
    differentiableAt_id.prodMk (differentiableAt_const y)
  have ht : DifferentiableAt ℝ (fun t => m t y) ρ := by
    have hh := hj.comp ρ hi
    exact hh
  have hs : Differentiable ℝ (m ρ) :=
    ((innerSL ℝ u).contDiff.comp (conditionalFieldMean_smooth hF x hr hl hρ0 hρ1)).differentiable (by simp)
  have htd : deriv (fun t => inner ℝ u y+r*t*m t y) ρ=
      r*m ρ y+(r*ρ)*deriv (fun t => m t y) ρ := by
    have hh := (hasDerivAt_const ρ (inner ℝ u y)).add
      (((hasDerivAt_id ρ).const_mul r).mul ht.hasDerivAt)
    simpa only [Pi.add_def,Pi.mul_def,id_eq,mul_one,zero_add] using hh.deriv
  have hsd : directional (conditionalFieldMean F x r ρ y)
      (fun z => inner ℝ u z+r*ρ*m ρ z) y=
      m ρ y+(r*ρ)*directional (conditionalFieldMean F x r ρ y) (m ρ) y := by
    unfold directional
    have hh := (innerSL ℝ u).hasFDerivAt.add ((hs y).hasFDerivAt.const_mul (r*ρ))
    change (fderiv ℝ (((innerSL ℝ u) : Point d → ℝ) + fun z => (r*ρ)*m ρ z) y) _=_
    rw [hh.fderiv]
    simp [m]
  change deriv (fun t => inner ℝ u y+r*t*m t y) ρ-
    r*directional (conditionalFieldMean F x r ρ y) (fun z => inner ℝ u z+r*ρ*m ρ z) y=
    r*ρ*(deriv (fun t => m t y) ρ-r*directional (conditionalFieldMean F x r ρ y) (m ρ) y)
  rw [htd,hsd]
  ring

theorem material_interpolation_score {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1) (u y : Point d) :
    materialScalar F x r (fun t z => inner ℝ u z+r*t*inner ℝ u (conditionalFieldMean F x r t z)) ρ y=
      r*tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i => JetCalculus.dir u (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
          (conditionalFieldMean F x r ρ z))) y := by
  rw [material_score_algebra hF x hr.le hl hρ0.le hρ1,
    material_conditionalFieldMean hF x hr hlam hl hρ0.le hρ1]
  have he : (fun i y => conditionalU F x r ρ y u ((lam:ℝ)*r)
      (fun _ : Unit => EuclideanSpace.basisFun (Fin d) ℝ i) [()])=
      fun i y => ρ⁻¹*JetCalculus.dir u (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
        (conditionalFieldMean F x r ρ z)) y := by
    funext i y
    rw [congrFun (conditionalU_one_eq_dir hF x hr hlam hl hρ0 hρ1 u _) y]
    rw [conditionalFieldMean_directional_symm hF x hr hl hρ0 hρ1]
  have hD (i : Fin d) : Differentiable ℝ (JetCalculus.dir u (fun z =>
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r ρ z))) :=
    (JetCalculus.smooth_dir ((innerSL ℝ _).contDiff.comp
      (conditionalFieldMean_smooth hF x hr.le hl hρ0.le hρ1)) u).differentiable (by simp)
  rw [he,tensorAdjoint_scalar _ _ hD]
  field_simp [hρ0.ne']

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

def jointSpace {d : ℕ} (i : Fin d) : ℝ × Point d :=
  (0,EuclideanSpace.basisFun (Fin d) ℝ i)

def jointMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (i : Fin d)
    (p : ℝ × Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (conditionalFieldMean F x r p.1 p.2)

def jointScore {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (i : Fin d)
    (p : ℝ × Point d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) p.2+r*p.1*jointMean F x r i p

lemma jointMean_smooth_at {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) {p : ℝ × Point d} (hp : p.1^2<1) (i : Fin d) :
    ContDiffAt ℝ (⊤:ℕ∞) (jointMean F x r i) p :=
  (innerSL ℝ _).contDiff.contDiffAt.comp p
    (conditionalFieldMean_joint_smooth hF x hr (by linarith) p hp)

lemma jointScore_smooth_at {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) {p : ℝ × Point d} (hp : p.1^2<1) (i : Fin d) :
    ContDiffAt ℝ (⊤:ℕ∞) (jointScore F x r i) p :=
  ((innerSL ℝ _).contDiff.contDiffAt.comp p contDiffAt_snd).add
    ((contDiffAt_const.mul contDiffAt_fst).mul (jointMean_smooth_at hF x hr hl hp i))

lemma joint_gadj_slice {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {V : Fin d → ℝ × Point d → ℝ} {y : Point d}
    (hV : ∀i,DifferentiableAt ℝ (V i) (ρ,y)) :
    JetCalculus.gadj jointSpace (jointScore F x r) V (ρ,y)=
      tensorAdjoint (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun i z => V i (ρ,z)) y := by
  unfold JetCalculus.gadj JetCalculus.cadj tensorAdjoint adjointCoordinate
  apply Finset.sum_congr rfl
  intro i _
  simp only [jointSpace]
  rw [←JetCalculus.dir_right_slice_at (hV i)]
  have hs : directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (interpolationPotential F x r ρ) y=jointScore F x r i (ρ,y) := by
    rw [directional_gradient,
      interpolationPotential_gradient hF x hr hl hρ0 hρ1]
    simp only [jointScore,jointMean,inner_add_left,real_inner_smul_left]
    congr 1
    · exact real_inner_comm _ _
    · congr 1
      exact real_inner_comm _ _
  rw [hs]
  rfl

lemma joint_score_transport {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (y : Point d) (i : Fin d) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k => JetCalculus.dir (jointSpace i) (jointMean F x r k)) (ρ,y) := by
  have hp : ρ^2<1 := by have := (probability_time hρ0.le hρ1).1; linarith
  have hm := joint_mdir_eq_material F x r ((jointScore_smooth_at hF x hr.le hl (p:=(ρ,y)) hp i).differentiableAt (by simp))
  change JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (jointScore F x r i) (ρ,y)=_ at hm
  rw [hm]
  rw [joint_gadj_slice hF x hr.le hl hρ0.le hρ1 (fun k =>
    (JetCalculus.smooth_dir_at (jointMean_smooth_at hF x hr.le hl hp k) _).differentiableAt (by simp))]
  have he : (fun k z => JetCalculus.dir (jointSpace i) (jointMean F x r k) (ρ,z))=
      fun k => JetCalculus.dir (EuclideanSpace.basisFun (Fin d) ℝ i)
        (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ k) (conditionalFieldMean F x r ρ z)) := by
    funext k z
    exact (JetCalculus.dir_right_slice_at
      ((jointMean_smooth_at hF x hr.le hl (p:=(ρ,z)) hp k).differentiableAt (by simp)) _).symm
  rw [he]
  exact material_interpolation_score hF x hr hlam hl hρ0 hρ1 _ y

theorem physical_material_adjoint {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    {V : Fin d → ℝ × Point d → ℝ} {y : Point d}
    (hV : ∀i,ContDiffAt ℝ (⊤:ℕ∞) (V i) (ρ,y)) :
    JetCalculus.mdir (1,0) jointSpace r (jointMean F x r)
      (JetCalculus.gadj jointSpace (jointScore F x r) V) (ρ,y)=
      JetCalculus.gadj jointSpace (jointScore F x r)
        (fun i => JetCalculus.mdir (1,0) jointSpace r (jointMean F x r) (V i)) (ρ,y)+
      r*JetCalculus.gadj jointSpace (jointScore F x r)
        (fun k p => ∑i,JetCalculus.dir (jointSpace i) (jointMean F x r k) p*V i p) (ρ,y) := by
  have hp : ρ^2<1 := by have := (probability_time hρ0.le hρ1).1; linarith
  exact JetCalculus.mdir_gadj_at _ _ _ (jointMean_smooth_at hF x hr.le hl hp)
    (jointScore_smooth_at hF x hr.le hl hp) hV (joint_score_transport hF x hr hlam hl hρ0 hρ1 y)

end LogConcaveSampling

end

end

end

end OAI
