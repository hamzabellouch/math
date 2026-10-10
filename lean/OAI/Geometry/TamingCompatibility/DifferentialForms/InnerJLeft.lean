import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitaryFrame

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_J_left (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v) (v w : E) :
    ⟪J v, w⟫ = -⟪v, J w⟫ := by
  have h := J.inner_map_map v (J w)
  rw [hJ, inner_neg_right] at h
  linarith

lemma inner_self_J (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v) (v : E) :
    ⟪v, J v⟫ = 0 := by
  have h := inner_J_left J hJ v v
  rw [real_inner_comm] at h
  linarith

lemma unit_pair (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v) {v : E}
    (hv : ‖v‖ = 1) : Orthonormal ℝ ![v,J v] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hv, inner_self_J J hJ, inner_J_left J hJ]

variable [FiniteDimensional ℝ E]

theorem exists_unitary_basis (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ b : OrthonormalBasis (Fin 4) ℝ E,
      J (b 0) = b 1 ∧ J (b 1) = -b 0 ∧ J (b 2) = b 3 ∧ J (b 3) = -b 2 := by
  classical
  let b₀ : OrthonormalBasis (Fin 4) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let v := b₀ 0
  have hv : ‖v‖ = 1 := b₀.orthonormal.norm_eq_one _
  let a : Fin 4 → E := ![v,J v,0,0]
  let s : Set (Fin 4) := {0,1}
  have ha : Orthonormal ℝ (s.domRestrict a) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i,hi⟩
    rcases j with ⟨j,hj⟩
    have hi' : i = 0 ∨ i = 1 := hi
    have hj' : j = 0 ∨ j = 1 := hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [s, a, Set.domRestrict, hv,
        inner_self_J J hJ, inner_J_left J hJ]
  obtain ⟨b,hb⟩ := ha.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  have hb0 : b 0 = v := hb 0 (by simp [s])
  have hb1 : b 1 = J v := hb 1 (by simp [s])
  let w := b 2
  have hw : ‖w‖ = 1 := b.orthonormal.norm_eq_one _
  have hvw : ⟪v,w⟫ = 0 := by
    rw [← hb0]
    exact b.orthonormal.inner_eq_zero (by decide : (0 : Fin 4) ≠ 2)
  have hJvw : ⟪J v,w⟫ = 0 := by
    rw [← hb1]
    exact b.orthonormal.inner_eq_zero (by decide : (1 : Fin 4) ≠ 2)
  have hvJw : ⟪v,J w⟫ = 0 := by
    have h := inner_J_left J hJ v w
    linarith
  have hwv : ⟪w,v⟫ = 0 := by rw [real_inner_comm, hvw]
  have hwJv : ⟪w,J v⟫ = 0 := by rw [real_inner_comm, hJvw]
  have hJwv : ⟪J w,v⟫ = 0 := by rw [real_inner_comm, hvJw]
  let c : Fin 4 → E := ![v,J v,w,J w]
  have hc : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [c, hv, hw, inner_self_J J hJ,
        hvw, hJvw, hvJw, hwv, hwJv, hJwv, inner_J_left J hJ, hJ]
  let b' := OrthonormalBasis.mk hc
    (hc.linearIndependent.span_eq_top_of_card_eq_finrank (by simpa using hdim.symm)).ge
  refine ⟨b', ?_⟩
  simp [b', OrthonormalBasis.coe_mk, c, hJ]

end TamingCompatibility.UnitaryBasis

open ContinuousAlternatingMap
namespace TamingCompatibility.GeometricSymbol
open UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev TwoForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E [⋀^Fin 2]→L[ℝ] ℝ

def coords (b : OrthonormalBasis (Fin 4) ℝ E) (α : TwoForm E) : W :=
  WithLp.toLp 2 ![α ![b 0,b 1], α ![b 0,b 2], α ![b 0,b 3],
    α ![b 1,b 2], α ![b 1,b 3], α ![b 2,b 3]]

lemma eval_swap (α : TwoForm E) (u v : E) : α ![v,u] = -α ![u,v] := by
  have hs : (![u,v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v,u] := by
    ext i; fin_cases i <;> simp
  simpa only [hs, ContinuousAlternatingMap.coe_toAlternatingMap] using
    α.toAlternatingMap.map_swap ![u,v] (show (0 : Fin 2) ≠ 1 by decide)

lemma eval_self (α : TwoForm E) (u : E) : α ![u,u] = 0 :=
  α.map_eq_zero_of_eq (v := ![u,u]) (i := 0) (j := 1) rfl (by decide)

lemma coords_injective (b : OrthonormalBasis (Fin 4) ℝ E) : Function.Injective (coords b) := by
  intro α β h
  have h0 := congrArg (fun a : W => a 0) h
  have h1 := congrArg (fun a : W => a 1) h
  have h2 := congrArg (fun a : W => a 2) h
  have h3 := congrArg (fun a : W => a 3) h
  have h4 := congrArg (fun a : W => a 4) h
  have h5 := congrArg (fun a : W => a 5) h
  dsimp [coords] at h0 h1 h2 h3 h4 h5
  have he : ∀ i j : Fin 4, α ![b i,b j] = β ![b i,b j] := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals try assumption
    all_goals simp only [eval_self]
    all_goals rw [eval_swap α, eval_swap β]; congr 1
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => b.toBasis)
  intro v
  change α (fun i => b (v i)) = β (fun i => b (v i))
  have hv : (fun i => b (v i)) = ![b (v 0), b (v 1)] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact he (v 0) (v 1)

def symbol (ξ : E) (α : TwoForm E) : TwoForm E :=
  alternatizeUncurryFin ((innerSL ℝ ξ).smulRight (α.curryLeft ξ))

lemma symbol_apply (ξ : E) (α : TwoForm E) (v w : E) :
    symbol ξ α ![v,w] = ⟪ξ,v⟫ * α ![ξ,w] - ⟪ξ,w⟫ * α ![ξ,v] := by
  rw [symbol, alternatizeUncurryFin_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, zero_add, pow_one,
    one_smul, neg_smul, add_zero]
  have h0 : Fin.removeNth (0 : Fin 2) ![v,w] = ![w] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![v,w] = ![v] := by ext i; fin_cases i; rfl
  change (((innerSL ℝ ξ).smulRight (α.curryLeft ξ)) v)
    (Fin.removeNth (0:Fin 2) ![v,w]) -
    (((innerSL ℝ ξ).smulRight (α.curryLeft ξ)) w)
    (Fin.removeNth (1:Fin 2) ![v,w]) = _
  rw [h0, h1]
  rfl

lemma eval_left (b : OrthonormalBasis (Fin 4) ℝ E) (α : TwoForm E) (ξ v : E) :
    α ![ξ,v] = ∑ i, b.repr ξ i * α ![b i,v] := by
  calc
    _ = (α.curryLeft (∑ i, b.repr ξ i • b i)) ![v] := by rw [b.sum_repr]; rfl
    _ = _ := by simp only [_root_.map_sum, _root_.map_smul, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, curryLeft_apply_apply]

lemma coords_symbol (b : OrthonormalBasis (Fin 4) ℝ E) (ξ : E) (α : TwoForm E) :
    coords b (symbol ξ α) = UnitaryFrame.wedge (b.repr ξ)
      (UnitaryFrame.interior (b.repr ξ) (coords b α)) := by
  have hi (i : Fin 4) : ⟪ξ,b i⟫ = b.repr ξ i := by
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  have h10 := eval_swap α (b 0) (b 1)
  have h20 := eval_swap α (b 0) (b 2)
  have h30 := eval_swap α (b 0) (b 3)
  have h21 := eval_swap α (b 1) (b 2)
  have h31 := eval_swap α (b 1) (b 3)
  have h32 := eval_swap α (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coords, symbol_apply, eval_left b α ξ, hi, UnitaryFrame.wedge, UnitaryFrame.interior,
      Fin.sum_univ_succ, eval_self, h10, h20, h30, h21, h31, h32] <;> ring

def antiInvariant (J : E →L[ℝ] E) (α : TwoForm E) : TwoForm E :=
  (1 / 2 : ℝ) • (α - α.compContinuousLinearMap J)

lemma eval_neg_left (α : TwoForm E) (u v : E) : α ![-u,v] = -α ![u,v] := by
  simpa only [neg_one_smul, smul_eq_mul, neg_one_mul] using
    α.vecCons_smul ![v] (-1 : ℝ) u

lemma eval_neg_right (α : TwoForm E) (u v : E) : α ![u,-v] = -α ![u,v] := by
  rw [eval_swap, eval_neg_left, eval_swap, neg_neg]

lemma coords_antiInvariant (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2) (α : TwoForm E) :
    coords b (antiInvariant J α) = UnitaryFrame.antiInvariantPart (coords b α) := by
  have hc (u v : E) : (α.compContinuousLinearMap J) ![u,v] = α ![J u,J v] := by
    change α (fun i => J (![u,v] i)) = _
    congr 1; ext i; fin_cases i <;> rfl
  have hs := eval_swap α (b 0) (b 1)
  have ht := eval_swap α (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coords, antiInvariant, UnitaryFrame.antiInvariantPart, UnitaryFrame.jAction, hc, h0,h1,h2,h3,
      eval_neg_left, eval_neg_right, hs, ht]

lemma coords_smul (b : OrthonormalBasis (Fin 4) ℝ E) (c : ℝ) (α : TwoForm E) :
    coords b (c • α) = c • coords b α := by
  ext i; fin_cases i <;> rfl

theorem closed_lift_principal_symbol [FiniteDimensional ℝ E]
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ v, J (J v) = -v)
    (hdim : Module.finrank ℝ E = 4) (ξ : E) (α : TwoForm E) :
    antiInvariant J.toContinuousLinearMap (symbol ξ (antiInvariant J.toContinuousLinearMap α)) =
      (‖ξ‖ ^ 2 / 2) • antiInvariant J.toContinuousLinearMap α := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_antiInvariant b _ h0 h1 h2 h3, coords_symbol,
    coords_antiInvariant b _ h0 h1 h2 h3, coords_smul,
    coords_antiInvariant b _ h0 h1 h2 h3, UnitaryFrame.closed_lift_principal_symbol]
  rw [b.repr.norm_map]

end TamingCompatibility.GeometricSymbol

end

end OAI
