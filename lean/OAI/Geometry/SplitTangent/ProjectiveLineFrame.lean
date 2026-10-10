import Mathlib
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.FormalBoxes

namespace OAI

/-! Projective Line Frame. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.ProjectiveEmbedding
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

 
def linearFrame (a : Fin (e.N+1) → ℂ) (x : X.Carrier) : Fin (e.N+1) → ℂ :=
  (∑i,a i*(e.map x).rep i)⁻¹ • (e.map x).rep

lemma linearFrame_eq_coordinates {a : Fin (e.N+1) → ℂ} {x : X.Carrier}
    {k : Fin (e.N+1)} (hk : (e.map x).rep k ≠ 0) :
    e.linearFrame a x = (∑i,a i*projectiveCoordinates k (e.map x) i)⁻¹ •
      projectiveCoordinates k (e.map x) := by
  have he : (∑i,a i*projectiveCoordinates k (e.map x) i)=
      ((e.map x).rep k)⁻¹ * ∑i,a i*(e.map x).rep i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [projectiveCoordinates]
    ring
  ext i
  simp only [linearFrame,Pi.smul_apply,smul_eq_mul]
  rw [he]
  simp only [projectiveCoordinates,mul_inv_rev,inv_inv]
  symm
  calc
    _ = (∑ j, a j*(e.map x).rep j)⁻¹ *
      (((e.map x).rep k * ((e.map x).rep k)⁻¹) * (e.map x).rep i) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hk,one_mul]

lemma linearFrame_denominator_ne {a v : Fin (e.N+1) → ℂ} {x : X.Carrier}
    (hv : e.Incidence x v) (ha : ∑i,a i*v i=1) :
    (∑i,a i*(e.map x).rep i) ≠ 0 := by
  obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep k ≠ 0 at hk
  have hvk : v k ≠ 0 := by
    intro hz
    have hvz : v=0 := by
      ext i
      rw [(e.incidence_iff_coordinates hk).mp hv i,hz,zero_mul]
      rfl
    simp [hvz] at ha
  have hcross : (∑i,a i*(e.map x).rep i)*v k=(e.map x).rep k := by
    calc
      _ = ∑i,a i*((e.map x).rep i*v k) := by rw [Finset.sum_mul]; congr 1; funext i; ring
      _ = ∑i,a i*((e.map x).rep k*v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hv k i]
      _ = (e.map x).rep k*(∑i,a i*v i) := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ = _ := by rw [ha,mul_one]
  intro h
  exact hk (by simpa only [h,zero_mul] using hcross.symm)

lemma linearFrame_eq_of_incidence {a v : Fin (e.N+1) → ℂ} {x : X.Carrier}
    (hv : e.Incidence x v) (ha : ∑i,a i*v i=1) : e.linearFrame a x=v := by
  have hden := e.linearFrame_denominator_ne hv ha
  ext j
  change (∑i,a i*(e.map x).rep i)⁻¹ * (e.map x).rep j=v j
  apply (inv_mul_eq_iff_eq_mul₀ hden).mpr
  calc
    _ = ∑i,a i*((e.map x).rep j*v i) := by
      rw [show (∑i,a i*((e.map x).rep j*v i))=
        (e.map x).rep j*(∑i,a i*v i) by rw [Finset.mul_sum]; congr 1; funext i; ring,ha,mul_one]
    _ = ∑i,a i*((e.map x).rep i*v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hv j i]
    _ = _ := by rw [Finset.sum_mul]; congr 1; funext i; ring

 
lemma linearFrame_change (a b : Fin (e.N+1) → ℂ) (x : X.Carrier)
    (hb : (∑i,b i*(e.map x).rep i)≠0) :
    e.linearFrame a x = (∑i,b i*e.linearFrame a x i) • e.linearFrame b x := by
  have he : (∑i,b i*e.linearFrame a x i)=
      (∑i,a i*(e.map x).rep i)⁻¹ * (∑i,b i*(e.map x).rep i) := by
    simp only [linearFrame,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ext i
  simp only [linearFrame,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma linearFrame_holomorphicAt
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : _root_.ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    {f : M → X.Carrier} {a : M → Fin (e.N+1) → ℂ} {y : M}
    (hf : ContMDiffAt I (ModelWithCorners X) ω f y)
    (ha : ContMDiffAt I 𝓘(ℂ,Fin (e.N+1) → ℂ) ω a y)
    (hn : (∑i,a y i*(e.map (f y)).rep i)≠0) :
    ContMDiffAt I 𝓘(ℂ,Fin (e.N+1) → ℂ) ω
      (fun z => e.linearFrame (a z) (f z)) y := by
  obtain ⟨k,hk⟩ := Function.ne_iff.mp (e.map (f y)).rep_nonzero
  change (e.map (f y)).rep k ≠ 0 at hk
  have hc := ((e.holomorphic k).contMDiffAt ((e.open_patch k).mem_nhds hk)).comp y hf
  have hd : ContMDiffAt I 𝓘(ℂ,ℂ) ω
      (fun z => ∑i,a z i*projectiveCoordinates k (e.map (f z)) i) y := by
    apply contMDiffAt_finsetSum
    intro i hi
    exact (contMDiffAt_pi_space.mp ha i).mul (contMDiffAt_pi_space.mp hc i)
  have hd0 : (∑i,a y i*projectiveCoordinates k (e.map (f y)) i)≠0 := by
    have he : (∑i,a y i*projectiveCoordinates k (e.map (f y)) i)=
        ((e.map (f y)).rep k)⁻¹ * (∑i,a y i*(e.map (f y)).rep i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [projectiveCoordinates]
      ring
    rw [he]
    exact mul_ne_zero (inv_ne_zero hk) hn
  apply ((hd.inv₀ hd0).smul hc).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds ((e.open_patch k).mem_nhds hk)] with z hz
  exact e.linearFrame_eq_coordinates hz

end SplitTangent.ProjectiveEmbedding

end

end OAI
