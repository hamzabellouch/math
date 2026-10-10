import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TorusStepFunctions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagGerms
open Classical

def FlagDirections (a : ℕ) (v w : ℝ × ℝ) : Prop :=
  ∀ j : Fin 4, cutForm a j v ≠ 0 ∨ cutForm a j w ≠ 0

theorem flagDirections_sector {a : ℕ} {v w : ℝ×ℝ} (h : FlagDirections a v w) :
    ∃ d : ℝ×ℝ, TransverseDirection a d ∧ ∀ j,
      (cutForm a j d<0 ↔ if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0) := by
  let σ : Fin 4 → Bool := fun j =>
    decide (if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0)
  have ha (j : Fin 4) (hj : cutForm a j v=0) :
      if σ j then cutForm a j (v+w)<0 else 0<cutForm a j (v+w) := by
    have hw : cutForm a j w≠0 := (h j).resolve_left (not_not.mpr hj)
    simp only [σ,hj,ite_eq_left,cutForm_add,zero_add]
    split_ifs with ht
    · exact of_decide_eq_true ht
    · exact lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr ht))) hw.symm
  have hi (j : Fin 4) (hj : cutForm a j v≠0) :
      if σ j then cutForm a j v<0 else 0<cutForm a j v := by
    simp only [σ,ite_eq_right hj]
    split_ifs with ht
    · exact of_decide_eq_true ht
    · exact lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr ht))) hj.symm
  obtain ⟨d,_,hd,hg⟩ := finite_arrangement_germ a id (fun _ => 0) v (v+w) σ
    ha hi Set.univ isOpen_univ (Set.mem_univ _)
  refine ⟨d,fun j => ?_,fun j => ?_⟩
  · simpa using hg j 0
  · have hh := hd j
    by_cases ht : if cutForm a j v=0 then cutForm a j w<0 else cutForm a j v<0
    · simpa [σ,ht] using hh
    · have hh' : 0<cutForm a j d := by simpa [σ,ht] using hh
      exact iff_of_false (not_lt_of_gt hh') ht

def SquareBoundary (v z : ℝ × ℝ) : Prop :=
  z.1 ∈ Set.Icc (0:ℝ) 1 ∧ z.2 ∈ Set.Icc (0:ℝ) 1 ∧
  (z.1=0 → 0<v.1) ∧ (z.1=1 → v.1<0) ∧
  (z.2=0 → 0<v.2) ∧ (z.2=1 → v.2<0)

def SquareFlag (a : ℕ) (v : ℝ × ℝ) :=
  {z : ℝ × ℝ // TransverseDirection a v ∧ SquareBoundary v z}

theorem sector_enters_square {a : ℕ} {v z : ℝ × ℝ}
    (hz : SquareBoundary v z) {p : GenericPlane a}
    (hp : p.val ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts z)
    (hv : p.val ∈ planeSector a z v) : SquareStep.InSquare p := by
  have h₀ (x d : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) (hd : x=0 → 0<d) :
      ¬(if x=0 then d<0 else x<0) := by
    split_ifs with he
    · exact not_lt_of_gt (hd he)
    · exact not_lt_of_ge hx.1
  have h₁ (x d : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) (hd : x=1 → d<0) :
      (if x=1 then d<0 else x<1) := by
    split_ifs with he
    · exact hd he
    · exact lt_of_le_of_ne hx.2 he
  have h l (hl : l∈SquareStep.squareEdgeCuts) := planeSign_neighborhood hp hv hl
  have hx₀ : ¬p.val.1<0 := by
    have hh := h (0,0) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₀ z.1 v.1 hz.1 hz.2.2.1] using hh'
  have hx₁ : p.val.1<1 := by
    have hh := h (0,1) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₁ z.1 v.1 hz.1 hz.2.2.2.1] using hh'
  have hy₀ : ¬p.val.2<0 := by
    have hh := h (1,0) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₀ z.2 v.2 hz.2.1 hz.2.2.2.2.1] using hh'
  have hy₁ : p.val.2<1 := by
    have hh := h (1,1) (by simp [SquareStep.squareEdgeCuts])
    have hh' := decide_eq_decide.mp hh
    simpa [planeSign,cutForm,h₁ z.2 v.2 hz.2.1 hz.2.2.2.2.2] using hh'
  exact ⟨⟨le_of_not_gt hx₀,hx₁⟩,⟨le_of_not_gt hy₀,hy₁⟩⟩

theorem squareSector_generic {a : ℕ} {v : ℝ × ℝ} (z : SquareFlag a v)
    {N : Set (ℝ×ℝ)} (hN : IsOpen N) (hz : z.val∈N) :
    ∃ p : GenericSquare a, p.val∈N ∧ p.val∈planeSector a z.val v := by
  obtain ⟨p,hp,hpv⟩ := planeSector_generic z.property.1
    (hN.inter (arrangementNeighborhood_open a SquareStep.squareEdgeCuts z.val))
    ⟨hz,self_mem_arrangementNeighborhood a SquareStep.squareEdgeCuts z.val⟩
  have hps := sector_enters_square z.property.2 hp.2 hpv
  exact ⟨⟨p.val,hps.1,hps.2,p.property⟩,hp.1,hpv⟩

def IsSquareGerm {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (z : SquareFlag a v) (c : K) : Prop :=
  ∃ N : Set (ℝ×ℝ), IsOpen N ∧ z.val∈N ∧
    ∀ p : GenericSquare a, p.val∈N → p.val∈planeSector a z.val v → f p=c

theorem exists_squareGerm {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) :
    ∃ c, IsSquareGerm f z c := by
  obtain ⟨S,hS⟩ := hf
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (arrangementNeighborhood_open a S z.val)
    (self_mem_arrangementNeighborhood a S z.val)
  refine ⟨f p,arrangementNeighborhood a S z.val,arrangementNeighborhood_open a S z.val,
    self_mem_arrangementNeighborhood a S z.val,fun q hq hqv => hS q p ?_⟩
  intro l hl
  exact (planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq hqv hl).trans
    (planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp hpv hl).symm

theorem IsSquareGerm.unique {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    {f : GenericSquare a → K} {z : SquareFlag a v} {c d : K}
    (hc : IsSquareGerm f z c) (hd : IsSquareGerm f z d) : c=d := by
  obtain ⟨N,hN,hz,hc⟩ := hc
  obtain ⟨M,hM,hz',hd⟩ := hd
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter hM) ⟨hz,hz'⟩
  exact (hc p hp.1 hpv).symm.trans (hd p hp.2 hpv)

noncomputable def flagValue {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) : K :=
  Classical.choose (exists_squareGerm f hf z)

theorem flagValue_spec {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v) :
    IsSquareGerm f z (flagValue f hf z) := Classical.choose_spec (exists_squareGerm f hf z)

theorem flagValue_eq {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (z : SquareFlag a v)
    {c : K} (hc : IsSquareGerm f z c) : flagValue f hf z=c := (flagValue_spec f hf z).unique hc

theorem flagValue_map {a : ℕ} {v : ℝ×ℝ} {K J : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) (t : K → J)
    (ht : HasSquareArrangement (t ∘ f)) (z : SquareFlag a v) :
    flagValue (t ∘ f) ht z=t (flagValue f hf z) := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf z
  exact flagValue_eq _ _ _ ⟨N,hN,hz,fun p hp hpv => congrArg t (hf' p hp hpv)⟩

theorem flagValue_finite {a : ℕ} {v : ℝ×ℝ} {ι K : Type*} [Finite ι]
    (f : ι → GenericSquare a → K) (hf : ∀ i, HasSquareArrangement (f i))
    (z : SquareFlag a v) {N : Set (ℝ×ℝ)} (hN : IsOpen N) (hz : z.val∈N) :
    ∃ p : GenericSquare a, p.val∈N ∧ p.val∈planeSector a z.val v ∧
      ∀ i, f i p=flagValue (f i) (hf i) z := by
  choose M hM hzM hfg using fun i => flagValue_spec (f i) (hf i) z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z
    (hN.inter (isOpen_iInter_of_finite hM)) ⟨hz,Set.mem_iInter.mpr hzM⟩
  exact ⟨p,hp.1,hpv,fun i => hfg i p (Set.mem_iInter.mp hp.2 i) hpv⟩

noncomputable def flagMem {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a)
    (z : SquareFlag a v) : Prop :=
  flagValue (fun p => decide (p∈U.val)) (polygon_hasSquareArrangement U.property) z=true

theorem flagMem_iff {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a) (z : SquareFlag a v) :
    ∃ N : Set (ℝ×ℝ), IsOpen N ∧ z.val∈N ∧
      ∀ p : GenericSquare a, p.val∈N → p.val∈planeSector a z.val v →
        (p∈U.val ↔ flagMem U z) := by
  obtain ⟨N,hN,hz,hf⟩ := flagValue_spec (fun p => decide (p∈U.val))
    (polygon_hasSquareArrangement U.property) z
  refine ⟨N,hN,hz,fun p hp hpv => ?_⟩
  unfold flagMem
  rw [← hf p hp hpv]
  simp

@[simp] theorem flagMem_bot {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    ¬flagMem (⊥ : polygonAlgebra a) z := by
  have h := flagValue_eq (fun p : GenericSquare a => decide (p∈(⊥ : polygonAlgebra a).val))
    (polygon_hasSquareArrangement (⊥ : polygonAlgebra a).property) z
    (c:=false) ⟨Set.univ,isOpen_univ,Set.mem_univ _,fun _ _ _ => by simp⟩
  intro hm
  exact Bool.false_ne_true (h.symm.trans hm)

theorem flagMem_sup {a : ℕ} {v : ℝ×ℝ} (U V : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem (U⊔V) z ↔ flagMem U z ∨ flagMem V z := by
  obtain ⟨N,hN,hz,h⟩ := flagMem_iff (U⊔V) z
  obtain ⟨M,hM,hz',h'⟩ := flagMem_iff U z
  obtain ⟨L,hL,hz'',h''⟩ := flagMem_iff V z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z ((hN.inter hM).inter hL) ⟨⟨hz,hz'⟩,hz''⟩
  rw [← h p hp.1.1 hpv,← h' p hp.1.2 hpv,← h'' p hp.2 hpv]
  rfl

theorem flagMem_compl {a : ℕ} {v : ℝ×ℝ} (U : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem Uᶜ z ↔ ¬flagMem U z := by
  obtain ⟨N,hN,hz,h⟩ := flagMem_iff Uᶜ z
  obtain ⟨M,hM,hz',h'⟩ := flagMem_iff U z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter hM) ⟨hz,hz'⟩
  rw [← h p hp.1 hpv,← h' p hp.2 hpv]
  rfl

theorem flagMem_halfPlane {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c : CutRing)
    (z : SquareFlag a v) :
    flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
      (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
  let U : polygonAlgebra a := ⟨halfPlane a j c,halfPlane_mem a j c⟩
  have hg : flagValue (fun p => decide (p∈U.val))
      (polygon_hasSquareArrangement U.property) z =
      decide (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
    apply flagValue_eq
    refine ⟨arrangementNeighborhood a {(j,c)} z.val,
      arrangementNeighborhood_open a {(j,c)} z.val,
      self_mem_arrangementNeighborhood a {(j,c)} z.val, fun p hp hpv => ?_⟩
    exact planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp hpv (Finset.mem_singleton_self _)
  change flagValue _ _ z=true ↔ _
  rw [hg]
  simp

end FlagGerms

end SimpleAmenable
end
end

end OAI
