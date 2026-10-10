import OAI.Analysis.IrrationalRotation.Model.Diagonal
import OAI.Analysis.IrrationalRotation.Analysis.StrongFieldContinuity

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

@[simp]
theorem diagonal_apply (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    diagonal a C hC ha v i = a i * v i := rfl

theorem norm_diagonal_le (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : ‖diagonal a C hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

@[simp]
theorem diagonal_single [DecidableEq I]
    (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (i : I) (z : ℂ) :
    diagonal a C hC ha (lp.single 2 i z) = lp.single 2 i (a i * z) := by
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

theorem strong_continuous_diagonal [TopologicalSpace X]
    (a : X → I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x i, ‖a x i‖ ≤ C)
    (hc : ∀ i, Continuous (fun x => a x i)) (v : SequenceHilbert I) :
    Continuous (fun x => diagonal (a x) C hC (ha x) v) := by
  classical
  let b : HilbertBasis I ℂ (SequenceHilbert I) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun _ => rfl
  apply InvariantProjection.strong_continuous_of_dense_span_of_bounded
    (b := b) (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    (fun x => norm_diagonal_le (a x) C hC (ha x)) v
  intro i
  simpa only [hb, diagonal_single, mul_one, Function.comp_def,
    lp.singleContinuousLinearMap_apply] using
    (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.comp (hc i)

end Invariant233.SequenceHilbert

namespace Invariant233

variable {I X : Type*} [TopologicalSpace X]

theorem isClosed_diagonal_relation
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsClosed {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  apply InvariantProjection.isClosed_zero_set_of_strong_continuous
  intro v
  have hleft : ∀ w, Continuous (fun t : X × X => (1 - p t.2) w) := by
    intro w
    have h : Continuous (fun t : X × X => w - p t.2 w) :=
      continuous_const.sub ((hp w).comp continuous_snd)
    simpa using h
  have hleftn : ∀ t : X × X,
      ‖1 - p t.2‖ ≤ ‖(1 : SequenceHilbert I →L[ℂ] SequenceHilbert I)‖ + C := by
    intro t
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hpn t.2))
  have hright : ∀ w, Continuous (fun t : X × X =>
      ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) w) := by
    intro w
    apply InvariantProjection.strong_continuous_comp_of_bounded
      (fun z => SequenceHilbert.strong_continuous_diagonal d B hB hd hdc z)
      (fun z => (hp z).comp continuous_fst)
      (fun t => SequenceHilbert.norm_diagonal_le (d t) B hB (hd t)) w
  exact InvariantProjection.strong_continuous_comp_of_bounded hleft hright hleftn v

theorem isCompact_diagonal_relation [CompactSpace X]
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} :=
  (isClosed_diagonal_relation p d B C hB hd hp hdc hpn).isCompact

theorem isCompact_diagonal_relation_on
    (Q : Set X) (hQ : IsCompact Q)
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, ContinuousOn (fun x => p x v) Q)
    (hdc : ∀ i, ContinuousOn (fun t => d t i) (Q ×ˢ Q))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X | t ∈ Q ×ˢ Q ∧
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let f : Q × Q → X × X := fun t => ((t.1 : X), (t.2 : X))
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let pQ : Q → SequenceHilbert I →L[ℂ] SequenceHilbert I := fun x => p x
  let dQ : (Q × Q) → I → ℂ := fun t => d (f t)
  have hpQ : ∀ v, Continuous (fun x : Q => pQ x v) := fun v => (hp v).domRestrict
  have hdQ : ∀ i, Continuous (fun t : Q × Q => dQ t i) := by
    intro i
    exact (hdc i).comp_continuous hf (fun t => ⟨t.1.property, t.2.property⟩)
  have hS := isCompact_diagonal_relation pQ dQ B C hB
    (fun t i => hd (f t) i) hpQ hdQ (fun x => hpn x)
  have himage := hS.image hf
  convert himage using 1
  ext t
  constructor
  · rintro ⟨ht, hzero⟩
    refine ⟨(⟨t.1, ht.1⟩, ⟨t.2, ht.2⟩), ?_, rfl⟩
    exact hzero
  · rintro ⟨q, hzero, rfl⟩
    exact ⟨⟨q.1.property, q.2.property⟩, hzero⟩

end Invariant233

end

end OAI
