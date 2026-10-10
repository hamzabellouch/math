import OAI.Analysis.StrictMeans.QuadraticIndex

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def second (u : ℂ → ℝ) (p v w : ℂ) : ℝ := fderiv ℝ (fderiv ℝ u) p v w

def hessianDet (u : ℂ → ℝ) (p : ℂ) : ℝ := second u p 1 1*second u p Complex.I Complex.I-(second u p 1 Complex.I)^2

def morseSign (u : ℂ → ℝ) (p : ℂ) : ℤ := if 0<hessianDet u p then 1 else -1

lemma smooth_morse_local_index {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p) (hp : fderiv ℝ u p=0)
    (htr : 0<second u p 1 1+second u p Complex.I Complex.I)
    (hD : hessianDet u p≠0) :
    ∃ R>0, ∀ r∈Ioo (0:ℝ) R, ∀ᶠ s in 𝓝 (0:ℝ), 0<s →
      ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v = morseSign u p := by
  let a := second u p 1 1
  let b := second u p 1 Complex.I
  let c := second u p Complex.I Complex.I
  let Q : ℂ → ℝ := fun z=>quadratic a b c (z-p)
  have hg : ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt (affinePotential u Q) L (t,z) ∧
        (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := local_quadratic_homotopy_regular hu hp hD
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hg
  refine ⟨R/2,by positivity,?_⟩
  intro r hr
  have ha := smooth_local_index_homotopy (affinePotential u Q)
    (fun z=>by
      dsimp only [affinePotential]
      exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)) hr.1 (p:=p) (by
      intro q hq
      have hd := mem_indexAnnulus.mp hq.2
      have hqR : q.2∈Metric.ball p R := by rw [Metric.mem_ball]; linarith [hr.2]
      apply hball hqR
      · intro he; rw [he,dist_self] at hd; linarith [hr.1]
      · exact hq.1)
  have hb := quadratic_local_index htr hD (p:=p) hr.1
  filter_upwards [ha,hb] with s hs hs'
  intro hspos o S hS
  have he := hs hspos o S hS
  have he' := hs' hspos o S hS
  simp only [affinePotential,sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] at he
  exact he.trans he'

end
end StrictInverseFirstPower.Grid

end

end OAI
