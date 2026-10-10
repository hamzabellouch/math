import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentAnchors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PlaneCornerKernel

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneCornerCoordinates
open Classical

abbrev PlaneSectorIndex := Fin 4 → Bool
noncomputable def planeDirectionSign (a : ℕ) (v : ℝ × ℝ) : PlaneSectorIndex :=
  fun j => decide (cutForm a j v<0)

noncomputable def planeDirectionRep (a : ℕ) (σ : PlaneSectorIndex) : ℝ × ℝ :=
  if h : ∃ v, TransverseDirection a v ∧ planeDirectionSign a v=σ then
    Classical.choose h else (-1,1)

theorem planeDirectionRep_transverse (a : ℕ) (σ : PlaneSectorIndex) :
    TransverseDirection a (planeDirectionRep a σ) := by
  unfold planeDirectionRep
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact plane_antidiagonal_transverse a

theorem planeDirectionRep_sign {a : ℕ} {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    planeDirectionSign a (planeDirectionRep a (planeDirectionSign a v))=planeDirectionSign a v := by
  have he : ∃ w, TransverseDirection a w ∧ planeDirectionSign a w=planeDirectionSign a v :=
    ⟨v,hv,rfl⟩
  rw [planeDirectionRep,dite_eq_left he]
  exact (Classical.choose_spec he).2

theorem transverse_neg_sign_congr {a : ℕ} {v w : ℝ × ℝ}
    (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (he : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    ∀ j, (cutForm a j (-v)<0 ↔ cutForm a j (-w)<0) := by
  intro j
  simp only [cutForm_neg,neg_lt_zero]
  constructor <;> intro h
  · by_contra! hh
    have ht := (he j).mpr (lt_of_le_of_ne hh (hw j))
    linarith
  · by_contra! hh
    have ht := (he j).mp (lt_of_le_of_ne hh (hv j))
    linarith

theorem planeCornerValue_congr_direction {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v w : ℝ × ℝ} (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (he : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    planeCornerValue f z v=planeCornerValue f z w := by
  unfold planeCornerValue planePairValue
  rw [planeGerm_congr_direction f z hv hw he,
    planeGerm_congr_direction f z hv.neg hw.neg (transverse_neg_sign_congr hv hw he)]

theorem planeCornerValue_rep {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    planeCornerValue f z (planeDirectionRep a (planeDirectionSign a v))=planeCornerValue f z v := by
  apply planeCornerValue_congr_direction f z (planeDirectionRep_transverse _ _) hv
  intro j
  exact decide_eq_decide.mp (congrFun (planeDirectionRep_sign hv) j)

theorem planeGerm_translate {a : ℕ} (f : PlaneStep a) (u : CutRing × CutRing)
    (z v : ℝ × ℝ) :
    planeGerm (PlaneStep.translate u f) z v=
      planeGerm f (z-(ordinary u.1,ordinary u.2)) v := by
  by_cases hv : TransverseDirection a v
  · apply planeGerm_eq hv
    obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f (z-(ordinary u.1,ordinary u.2)) v hv
    refine ⟨(fun p => p-(ordinary u.1,ordinary u.2)) ⁻¹' N,
      hN.preimage (continuous_id.sub continuous_const),hz,fun p hp hpv => ?_⟩
    have he : (GenericPlane.shift (-u) p).val=p.val-(ordinary u.1,ordinary u.2) := by
      ext <;> simp [GenericPlane.shift,sub_eq_add_neg]
    apply hf (GenericPlane.shift (-u) p)
    · rw [he]; exact hp
    · intro j
      have hj := hpv j
      rw [he,cutForm_sub,cutForm_sub]
      split_ifs with ht
      · rw [ite_eq_left ht] at hj; linarith
      · rw [ite_eq_right ht] at hj; linarith
  · simp [planeGerm,hv]

theorem planeCornerValue_translate {a : ℕ} (f : PlaneStep a) (u : CutRing × CutRing)
    (z v : ℝ × ℝ) :
    planeCornerValue (PlaneStep.translate u f) z v=
      planeCornerValue f (z-(ordinary u.1,ordinary u.2)) v := by
  simp only [planeCornerValue,planePairValue,planeGerm_translate]

abbrev PlaneCornerIndex (a : ℕ) := VertexType (commonVertexDenominator a) × PlaneSectorIndex

noncomputable def planeVertexPosition (a : ℕ) (t : VertexType (commonVertexDenominator a))
    (u : Multiplicative (CutRing × CutRing)) : ℝ × ℝ :=
  vertexRepresentative (commonVertexDenominator a) t+(ordinary u.toAdd.1,ordinary u.toAdd.2)

theorem planeVertexPosition_injective (a : ℕ) (t : VertexType (commonVertexDenominator a)) :
    Function.Injective (planeVertexPosition a t) := by
  intro u v h
  have he := add_left_cancel h
  have h₁ := ordinary_injective (congrArg Prod.fst he)
  have h₂ := ordinary_injective (congrArg Prod.snd he)
  exact congrArg Multiplicative.ofAdd (Prod.ext h₁ h₂)

theorem planeCorner_coordinates_finite {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) :
    (Function.support (fun u => planeCornerValue f (planeVertexPosition a t.1 u)
      (planeDirectionRep a t.2))).Finite := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  apply ((planeArrangementVertices a S).finite_toSet.preimage
    (planeVertexPosition_injective a t.1).injOn).subset
  intro u hu
  exact planeCornerValue_mem_vertices ha f hS (planeDirectionRep_transverse a t.2) hu

noncomputable def planeCornerCoordinates {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) : PolygonGroupRing :=
  MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite
    (fun u => planeCornerValue f (planeVertexPosition a t.1 u) (planeDirectionRep a t.2))
    (planeCorner_coordinates_finite ha f t))

@[simp] theorem planeCornerCoordinates_coeff {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (t : PlaneCornerIndex a) (u : Multiplicative (CutRing × CutRing)) :
    (planeCornerCoordinates ha f t).coeff u=
      planeCornerValue f (planeVertexPosition a t.1 u) (planeDirectionRep a t.2) := rfl

theorem planeCornerCoordinates_injective_zero {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (hc : ∀ t, planeCornerCoordinates ha f t=0) : f=0 := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  apply planeCornerValue_injective_zero f
  intro z v hv
  by_contra hn
  obtain ⟨l,hl,k,hk,hdir,hzl,hzk⟩ := planeCornerValue_exists_incident f hS hv hn
  obtain ⟨t,x,y,hz⟩ := all_intersections_finite_templates ha l.1 k.1 hdir l.2 k.2 z hzl hzk
  have he := congrArg (fun q : PolygonGroupRing => q.coeff (Multiplicative.ofAdd (x,y)))
    (hc (t,planeDirectionSign a v))
  change planeCornerValue f (planeVertexPosition a t (Multiplicative.ofAdd (x,y)))
    (planeDirectionRep a (planeDirectionSign a v))=0 at he
  rw [planeCornerValue_rep f _ hv] at he
  exact hn (hz ▸ he)

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
