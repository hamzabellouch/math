import OAI.MathematicalPhysics.Transonic.Phase.Profile

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology

lemma primitive_hasDerivWithinAt_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {x : ℝ} (hx : 0≤x) :
    HasDerivWithinAt (fun z => ∫ q in (0:ℝ)..z, f q) (f x) (Ici 0) x := by
  have hc : ContinuousOn f (Icc 0 (x+1)) := hf.mono (fun _ ht => ht.1)
  have hxi : x∈Icc (0:ℝ) (x+1) := ⟨hx,by linarith⟩
  have : Fact (x∈Icc (0:ℝ) (x+1)) := ⟨hxi⟩
  have hInt : IntervalIntegrable f MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact hf.mono (fun _ ht => ht.1)
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s:=Icc (0:ℝ) (x+1)) hInt
    (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hc x hxi)
  apply hd.mono_of_mem_nhdsWithin
  change Ici (0:ℝ) ∩ Iic (x+1) ∈ 𝓝[Ici (0:ℝ)] x
  exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))

lemma primitive_contDiffOn_Ici {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ici 0)) :
    ContDiffOn ℝ ∞ (fun z => ∫ q in (0:ℝ)..z, f q) (Ici 0) := by
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici (0:ℝ))]
  have hd := fun x hx => primitive_hasDerivWithinAt_Ici hf.continuousOn (x:=x) hx
  refine ⟨fun x hx => (hd x hx).differentiableWithinAt,?_⟩
  exact hf.congr (fun x hx => (hd x hx).derivWithin (uniqueDiffOn_Ici (0:ℝ) x hx))

def GlobalProfile.radialIntegrand (P : GlobalProfile) (x : ℝ) : ℝ := P.g x/(1-x*P.g x)
def GlobalProfile.radialPrimitive (P : GlobalProfile) (x : ℝ) : ℝ :=
  ∫ q in (0:ℝ)..x, P.radialIntegrand q
def GlobalProfile.radialH (P : GlobalProfile) (x : ℝ) : ℝ :=
  (1/P.b)*Real.exp (P.b/2*P.radialPrimitive x)

lemma GlobalProfile.radial_pole_pos (P : GlobalProfile) {x : ℝ} (hx : 0≤x) : 0<1-x*P.g x := by
  have hp := P.pole_pos (Real.sqrt x)
  have he : Real.sqrt x*P.velocity (Real.sqrt x)=x*P.g x := by
    rw [GlobalProfile.velocity,Real.sq_sqrt hx,← mul_assoc,← sq,Real.sq_sqrt hx]
  rwa [he] at hp

lemma GlobalProfile.radialIntegrand_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ P.radialIntegrand (Ici 0) :=
  P.smooth.div (contDiffOn_const.sub (contDiffOn_id.mul P.smooth))
    (fun _ hx => ne_of_gt (P.radial_pole_pos hx))
lemma GlobalProfile.radialPrimitive_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ P.radialPrimitive (Ici 0) :=
  primitive_contDiffOn_Ici P.radialIntegrand_smooth
lemma GlobalProfile.radialPrimitive_derivative (P : GlobalProfile) {x : ℝ} (hx : 0≤x) :
    HasDerivWithinAt P.radialPrimitive (P.radialIntegrand x) (Ici 0) x :=
  primitive_hasDerivWithinAt_Ici P.radialIntegrand_smooth.continuousOn hx
lemma GlobalProfile.radialH_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialH (Ici 0) :=
  contDiffOn_const.mul (contDiffOn_const.mul P.radialPrimitive_smooth).exp

lemma GlobalProfile.radialPrimitive_chain (P : GlobalProfile) (y : ℝ) :
    HasDerivAt (fun q => (1/2:ℝ)*P.radialPrimitive (q^2)) (P.integrand y) y := by
  have hd := (P.radialPrimitive_derivative (sq_nonneg y)).comp_hasDerivAt (h:=fun q : ℝ => q^2) y
    ((hasDerivAt_id y).pow 2) (Filter.Eventually.of_forall (fun q => sq_nonneg q))
  convert hd.const_mul (1/2:ℝ) using 1 <;> try rfl
  dsimp only [GlobalProfile.integrand,GlobalProfile.radialIntegrand,GlobalProfile.velocity]
  norm_num only [Nat.cast_ofNat,pow_one,one_mul,id_eq]
  have he : 1-y*(y*P.g (y^2))=1-y^2*P.g (y^2) := by ring
  rw [he]
  ring

lemma GlobalProfile.primitive_radial (P : GlobalProfile) (y : ℝ) :
    P.primitive y=(1/2:ℝ)*P.radialPrimitive (y^2) := by
  let F := fun q => P.primitive q-(1/2:ℝ)*P.radialPrimitive (q^2)
  have hd (q : ℝ) : HasDerivAt F 0 q := by
    convert (P.primitive_derivative q).sub (P.radialPrimitive_chain q) using 1
    ring
  have he := is_const_of_deriv_eq_zero (fun q => (hd q).differentiableAt) (fun q => (hd q).deriv) y 0
  have hz : F 0=0 := by simp [F,GlobalProfile.primitive,GlobalProfile.radialPrimitive]
  rw [hz] at he
  exact sub_eq_zero.mp he

lemma GlobalProfile.H_radial (P : GlobalProfile) (y : ℝ) : P.H y=P.radialH (y^2) := by
  unfold GlobalProfile.H GlobalProfile.radialH
  rw [P.primitive_radial]
  congr 2
  ring

end SepticProfile

end
end

end OAI
