import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Zariski Pair Open. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent

lemma bihomogeneous_eval_scale {N a b : ℕ} (p : PairPolynomial N)
    (hp : ∀ m∈p.support, (∑i : Fin (N+1),m (0,i))=a ∧ (∑i : Fin (N+1),m (1,i))=b)
    (v : Fin 2 × Fin (N+1) → ℂ) (s t : ℂ) :
    MvPolynomial.eval (fun k => (if k.1=0 then s else t)*v k) p =
      (s^a*t^b)*MvPolynomial.eval v p := by
  classical
  rw [MvPolynomial.eval_eq',MvPolynomial.eval_eq']
  change (∑m∈p.support, p.coeff m * ∏k, ((if k.1=0 then s else t)*v k)^(m k)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow,Finset.prod_mul_distrib]
  have he : (∏k : Fin 2 × Fin (N+1), (if k.1=0 then s else t)^(m k)) = s^a*t^b := by
    rw [Fintype.prod_prod_type,Fin.prod_univ_two]
    norm_num only [↓reduceIte,Fin.one_eq_zero_iff]
    rw [Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,(hp m hm).1,(hp m hm).2]
  rw [he]
  ring

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

lemma isOpen_pairEval_ne_zero (p : PairPolynomial e.N) (hp : Bihomogeneous p) :
    IsOpen {xy | pairEval e p xy≠0} := by
  classical
  obtain ⟨a,b,hp⟩ := hp
  apply isOpen_iff_mem_nhds.mpr
  intro xy hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map xy.1).rep_nonzero
  obtain ⟨j,hj⟩ := Function.ne_iff.mp (e.map xy.2).rep_nonzero
  let q : X.Carrier × X.Carrier → ℂ := fun uv => MvPolynomial.eval
    (fun k : Fin 2 × Fin (e.N+1) => if k.1=0 then projectiveCoordinates i (e.map uv.1) k.2
      else projectiveCoordinates j (e.map uv.2) k.2) p
  have hq : ContinuousAt q xy := by
    apply (MvPolynomial.continuous_eval p).continuousAt.comp
    apply continuousAt_pi.mpr
    intro k
    split_ifs
    · exact (continuous_apply k.2).continuousAt.comp
        (((e.holomorphic i).continuousOn.continuousAt ((e.open_patch i).mem_nhds hi)).comp continuous_fst.continuousAt)
    · exact (continuous_apply k.2).continuousAt.comp
        (((e.holomorphic j).continuousOn.continuousAt ((e.open_patch j).mem_nhds hj)).comp continuous_snd.continuousAt)
  have hscale (uv : X.Carrier × X.Carrier) : q uv =
      ((e.map uv.1).rep i)⁻¹^a * ((e.map uv.2).rep j)⁻¹^b * pairEval e p uv := by
    have hfun : (fun k : Fin 2 × Fin (e.N+1) =>
        if k.1=0 then projectiveCoordinates i (e.map uv.1) k.2
        else projectiveCoordinates j (e.map uv.2) k.2) =
        (fun k : Fin 2 × Fin (e.N+1) =>
          (if k.1=0 then ((e.map uv.1).rep i)⁻¹ else ((e.map uv.2).rep j)⁻¹) *
          (if k.1=0 then (e.map uv.1).rep k.2 else (e.map uv.2).rep k.2)) := by
      funext k
      split_ifs <;> rfl
    change MvPolynomial.eval _ p = _
    rw [hfun]
    exact bihomogeneous_eval_scale p hp _ _ _
  have hqne : q xy≠0 := by
    rw [hscale]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero a (inv_ne_zero hi)) (pow_ne_zero b (inv_ne_zero hj))) hxy
  apply mem_of_superset (hq.eventually_ne hqne)
  intro uv huv
  change pairEval e p uv≠0
  intro he
  exact huv (by rw [hscale,he,mul_zero])

theorem IsZariskiOpenPair.isOpen {U : Set (X.Carrier × X.Carrier)} (hU : IsZariskiOpenPair e U) :
    IsOpen U := by
  obtain ⟨S,hS,rfl⟩ := hU
  have heq : {xy | ∃p∈S,pairEval e p xy≠0} = ⋃p∈S,{xy | pairEval e p xy≠0} := by ext; simp
  rw [heq]
  exact isOpen_iUnion (fun p => isOpen_iUnion (fun hp => isOpen_pairEval_ne_zero e p (hS p hp)))

end SplitTangent

end

end OAI
