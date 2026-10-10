import OAI.Analysis.StrictMeans.DiagonalIndex

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma StarCertificate.joint {u : ℝ × ℂ → ℝ} {t s : ℝ} {p : ℂ}
    (h : StarCertificate u (t,p) (0,1) (0,Complex.I) s) :
    StarCertificate (fun z=>u (t,z)) p 1 Complex.I s := by
  simpa only [StarCertificate,Prod.smul_mk,smul_zero,Prod.mk_add_mk,Prod.mk_sub_mk,
    add_zero,sub_zero,zero_add] using h

def indexAnnulus (p : ℂ) (r : ℝ) : Set ℂ :=
  Metric.closedBall p (3*r/2) \ Metric.ball p (r/2)

lemma compact_indexAnnulus (p : ℂ) (r : ℝ) : IsCompact (indexAnnulus p r) :=
  (isCompact_closedBall p (3*r/2)).diff Metric.isOpen_ball

lemma mem_indexAnnulus {p z : ℂ} {r : ℝ} : z ∈ indexAnnulus p r ↔
    r/2 ≤ dist z p ∧ dist z p ≤ 3*r/2 := by
  simp only [indexAnnulus,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,not_lt]
  exact and_comm

lemma smooth_local_index_homotopy (u : ℝ × ℂ → ℝ) (hc : ∀ z, Continuous (fun t : ℝ => u (t,z)))
    {p : ℂ} {r : ℝ} (hr : 0<r)
    (hd : ∀ q∈ (Icc (0:ℝ) 1) ×ˢ indexAnnulus p r,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt u L q ∧
        (L (0,1)≠0 ∨ L (0,Complex.I)≠0)) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) →
      ∑ v∈S, heightIndex (fun w=>u (0,meshPoint o s w)) ex ey v =
      ∑ v∈S, heightIndex (fun w=>u (1,meshPoint o s w)) ex ey v := by
  have hk : IsCompact ((Icc (0:ℝ) 1) ×ˢ indexAnnulus p r) := isCompact_Icc.prod (compact_indexAnnulus p r)
  have hn₀ : ‖((0,1):ℝ × ℂ)‖≤1 := by simp
  have hn₁ : ‖((0,Complex.I):ℝ × ℂ)‖≤1 := by simp
  have hcert := compact_regular_star hk hn₀ hn₁ hd
  filter_upwards [hcert,gt_mem_nhds (show (0:ℝ)<r/8 by positivity)] with s hs hsbound
  intro hspos o S hS
  let a : Icc (0:ℝ) 1 := ⟨0,by simp⟩
  let b : Icc (0:ℝ) 1 := ⟨1,by simp⟩
  apply local_index_homotopy (fun t : Icc (0:ℝ) 1 => fun v=>u (t,meshPoint o s v))
    (fun v=>(hc (meshPoint o s v)).comp continuous_subtype_val)
    ex_ne_zero ey_ne_zero ex_add_ey_ne_zero S ?_ a b
  intro t v hv
  have hb := meshBoundary_annulus hS hv
  rw [abs_of_pos hspos] at hb
  have hvK : meshPoint o s v∈ indexAnnulus p r := by
    rw [mem_indexAnnulus]
    constructor <;> linarith
  exact (StarCertificate.joint (hs ((t:ℝ),meshPoint o s v) ⟨t.property,hvK⟩ hspos)).toRegularStar

end
end StrictInverseFirstPower.Grid

end

end OAI
