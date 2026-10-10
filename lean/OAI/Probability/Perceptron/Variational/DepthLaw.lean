import Mathlib
import OAI.Probability.Perceptron.Variational.LabelReference

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

def indexedInfiniteLeafMeasure (k : ℕ) (z : Fin k → ℝ) :
    Measure (IndexedCascadeBase k × (ℕ → IndexedLeaf k)) :=
  (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) ⊗ₘ
    kernelInfiniteReplica (indexedLeafKernel k) ℕ

instance indexedInfiniteLeafMeasure_probability (k : ℕ) (z : Fin k → ℝ) :
    IsProbabilityMeasure (indexedInfiniteLeafMeasure k z) := by
  unfold indexedInfiniteLeafMeasure
  infer_instance

def indexedDepthArray (k : ℕ) (xs : ℕ → IndexedLeaf k) : FiniteOverlap (Fin (k+1)) :=
  fun i j => indexedCommonDepth k (xs i) (xs j)

lemma indexedDepthArray_measurable (k : ℕ) : Measurable (indexedDepthArray k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun xs : ℕ → IndexedLeaf k => indexedCommonDepth k (xs i) (xs j))
  have hf : Measurable (fun p : IndexedLeaf k × IndexedLeaf k => indexedCommonDepth k p.1 p.2) :=
    measurable_of_countable _
  have hg : Measurable (fun xs : ℕ → IndexedLeaf k => (xs i,xs j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact hf.comp hg

def indexedDepthLaw (k : ℕ) (z : Fin k → ℝ) : ProbabilityMeasure (FiniteOverlap (Fin (k+1))) :=
  ⟨(indexedInfiniteLeafMeasure k z).map (fun a => indexedDepthArray k a.2),
    inferInstance⟩

lemma indexedDepthLaw_lintegral (k : ℕ) (z : Fin k → ℝ)
    (F : FiniteOverlap (Fin (k+1)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ R, F R ∂(indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))) =
      ∫⁻ b, ∫⁻ xs, F (indexedDepthArray k xs)
        ∂Measure.infinitePi (fun _ : ℕ => indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  change (∫⁻ R, F R ∂(indexedInfiniteLeafMeasure k z).map
    (fun a => indexedDepthArray k a.2)) = _
  calc
    _ = ∫⁻ a, F (indexedDepthArray k a.2) ∂indexedInfiniteLeafMeasure k z :=
      lintegral_map hF ((indexedDepthArray_measurable k).comp measurable_snd)
    _ = _ := by
      exact Measure.lintegral_compProd (hF.comp ((indexedDepthArray_measurable k).comp measurable_snd))

lemma indexedDepthLaw_lintegral_prefix (k : ℕ) (z : Fin k → ℝ) (r : ℕ)
    (F : FiniteBlock (Fin (k+1)) r → ℝ≥0∞) :
    (∫⁻ R, F (finiteBlock r R) ∂(indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))) =
      ∫⁻ b, ∫⁻ xs : Fin r → IndexedLeaf k,
        F (fun i j => indexedCommonDepth k (xs i) (xs j))
        ∂Measure.pi (fun _ => indexedLeafProbability k b) ∂indexedCascadeBaseLaw k z := by
  have hF : Measurable F := measurable_of_countable _
  refine (indexedDepthLaw_lintegral k z (fun R => F (finiteBlock r R))
    (hF.comp (finiteBlock_measurable r))).trans ?_
  apply lintegral_congr
  intro b
  exact (infiniteReplica_prefix_preserving (indexedLeafProbability k b) r).lintegral_comp
    (measurable_of_countable (fun xs : Fin r → IndexedLeaf k =>
      F (fun i j => indexedCommonDepth k (xs i) (xs j))))

lemma infiniteReplica_prefix_fresh_preserving {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (fun xs : ℕ → S => ((fun i : Fin r => xs i.val),xs r))
      (Measure.infinitePi (fun _ : ℕ => μ)) ((Measure.pi (fun _ : Fin r => μ)).prod μ) := by
  have hfinite := measurePreserving_piFinSuccAbove (fun _ : Fin (r+1) => μ) (Fin.last r)
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := Measure.pi (fun _ : Fin r => μ))).comp
    (hfinite.comp (infiniteReplica_prefix_preserving μ (r+1)))
  convert h using 1
  funext xs
  simp only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply]
  apply Prod.ext
  · funext i
    simp [Fin.init]
  · rfl

lemma indexedDepthLaw_geometry (k : ℕ) (z : Fin k → ℝ) :
    ∀ᵐ R ∂(indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))),
      (∀ i j, R i j = R j i) ∧ (∀ i, R i i = Fin.last k) ∧
        ∀ i j l, min (R i j) (R i l) ≤ R j l := by
  apply (ae_map_iff ((indexedDepthArray_measurable k).comp measurable_snd).aemeasurable
    (by measurability)).mpr
  exact ae_of_all _ fun a => ⟨fun i j => indexedCommonDepth_comm k _ _,
    fun i => indexedCommonDepth_self k _,fun i j l => indexedCommonDepth_ultrametric k _ _ _⟩

def CascadeShapeReplicas : (n : ℕ) → CascadeVisitShape n → Type
  | 0, r => Fin r
  | n + 1, ss => Σ i : Fin ss.length, CascadeShapeReplicas n ss[i]

instance cascadeShapeReplicas_fintype (n : ℕ) (s : CascadeVisitShape n) :
    Fintype (CascadeShapeReplicas n s) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin s))
  | succ n ih =>
    letI (i : Fin s.length) := ih s[i]
    exact inferInstanceAs (Fintype (Σ i : Fin s.length, CascadeShapeReplicas n s[i]))

def cascadeShapeLeaves : (n : ℕ) → (s : CascadeVisitShape n) →
    CascadeShapeReplicas n s → IndexedLeaf n
  | 0, _, _ => ()
  | n + 1, ss, i => (i.1.val, 0, cascadeShapeLeaves n ss[i.1] i.2)

lemma cascadeShapeReplicas_nonempty (n : ℕ) (s : CascadeVisitShape n)
    (hs : s.Valid n) : Nonempty (CascadeShapeReplicas n s) := by
  induction n with
  | zero => exact ⟨⟨0, hs⟩⟩
  | succ n ih =>
    have hlen : 0 < s.length := List.length_pos_iff.mpr hs.1
    obtain ⟨x⟩ := ih s[0] (hs.2 _ (List.getElem_mem hlen))
    exact ⟨⟨⟨0, hlen⟩, x⟩⟩

lemma cascadeShapeReplicas_card (n : ℕ) (s : CascadeVisitShape n) :
    Fintype.card (CascadeShapeReplicas n s) = cascadeVisitCount n s := by
  induction n with
  | zero => exact Fintype.card_fin s
  | succ n ih =>
    change Fintype.card (Σ i : Fin s.length, CascadeShapeReplicas n s[i]) = _
    rw [Fintype.card_sigma]
    simp_rw [ih]
    change (∑ i : Fin s.length, cascadeVisitCount n s[i]) = (s.map (cascadeVisitCount n)).sum
    rw [← List.sum_ofFn]
    simp

def cascadeShapeReplicasOfFnEquiv (n m : ℕ) (s : Fin m → CascadeVisitShape n) :
    (Σ i : Fin m, CascadeShapeReplicas n (s i)) ≃
      CascadeShapeReplicas (n + 1) (List.ofFn s) := by
  change (Σ i : Fin m, CascadeShapeReplicas n (s i)) ≃
    (Σ i : Fin (List.ofFn s).length, CascadeShapeReplicas n (List.ofFn s)[i])
  refine Equiv.sigmaCongr (finCongr (List.length_ofFn).symm) (fun i => ?_)
  exact Equiv.cast (by simp)

lemma cascadeShapeLeaves_cast (n : ℕ) {s t : CascadeVisitShape n}
    (h : s = t) (x : CascadeShapeReplicas n s) :
    cascadeShapeLeaves n t (cast (congrArg (CascadeShapeReplicas n) h) x) =
      cascadeShapeLeaves n s x := by
  cases h
  rfl

lemma cascadeShapeLeaves_ofFn (n m : ℕ) (s : Fin m → CascadeVisitShape n)
    (i : Fin m) (x : CascadeShapeReplicas n (s i)) :
    cascadeShapeLeaves (n + 1) (List.ofFn s)
      (cascadeShapeReplicasOfFnEquiv n m s ⟨i,x⟩) =
        (i.val, 0, cascadeShapeLeaves n (s i) x) := by
  simp only [cascadeShapeReplicasOfFnEquiv, Equiv.sigmaCongr, cascadeShapeLeaves]
  change (i.val, 0, cascadeShapeLeaves n _ (cast _ x)) = _
  have h : (List.ofFn s)[(finCongr (List.length_ofFn).symm) i] = s i := by simp
  congr 2
  exact cascadeShapeLeaves_cast n h.symm x

theorem finite_leaf_tuple_shape (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (xs : ι → IndexedLeaf n),
      ∃ s : CascadeVisitShape n, s.Valid n ∧
        ∃ e : ι ≃ CascadeShapeReplicas n s,
          ∀ i j, indexedCommonDepth n (xs i) (xs j) =
            indexedCommonDepth n (cascadeShapeLeaves n s (e i))
              (cascadeShapeLeaves n s (e j)) := by
  classical
  induction n with
  | zero =>
    intro ι _ _ xs
    exact ⟨Fintype.card ι, Fintype.card_pos, Fintype.equivFin ι, fun _ _ => rfl⟩
  | succ n ih =>
    intro ι _ _ xs
    let root : ι → ℕ × ℕ := fun i => ((xs i).1, (xs i).2.1)
    let V := Set.range root
    let : Fintype V := (Set.finite_range root).fintype
    let g₀ : ι → V := fun i => ⟨root i, ⟨i,rfl⟩⟩
    have hg₀ : Function.Surjective g₀ := by
      rintro ⟨v, i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
    let : Nonempty V := Nonempty.map g₀ inferInstance
    let g : ι → Fin (Fintype.card V) := fun i => Fintype.equivFin V (g₀ i)
    have hg : Function.Surjective g := (Fintype.equivFin V).surjective.comp hg₀
    have hroot (i j : ι) : g i = g j ↔ (xs i).1 = (xs j).1 ∧ (xs i).2.1 = (xs j).2.1 := by
      change (Fintype.equivFin V) (g₀ i) = (Fintype.equivFin V) (g₀ j) ↔ _
      rw [Equiv.apply_eq_iff_eq, Subtype.ext_iff]
      exact Prod.ext_iff
    let J (a : Fin (Fintype.card V)) := {i : ι // g i = a}
    let (a : Fin (Fintype.card V)) : Nonempty (J a) :=
      ⟨⟨Classical.choose (hg a), Classical.choose_spec (hg a)⟩⟩
    have hc (a : Fin (Fintype.card V)) := ih (J a) (fun i => (xs i.val).2.2)
    choose ss hv ee he using hc
    let s : CascadeVisitShape (n + 1) := List.ofFn ss
    have hs : s.Valid (n + 1) := by
      constructor
      · have hp : 0 < Fintype.card V := Fintype.card_pos
        apply List.length_pos_iff.mp
        simpa only [s, List.length_ofFn] using hp
      · intro t ht
        obtain ⟨a, rfl⟩ := List.mem_ofFn.mp ht
        exact hv a
    let E : ι ≃ CascadeShapeReplicas (n + 1) s :=
      ((Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight ee)).trans
        (cascadeShapeReplicasOfFnEquiv n (Fintype.card V) ss)
    refine ⟨s, hs, E, ?_⟩
    intro i j
    obtain ⟨⟨a,i⟩, rfl⟩ := (Equiv.sigmaFiberEquiv g).surjective i
    obtain ⟨⟨b,j⟩, rfl⟩ := (Equiv.sigmaFiberEquiv g).surjective j
    have hE (a : Fin (Fintype.card V)) (i : J a) :
        cascadeShapeLeaves (n + 1) s (E ((Equiv.sigmaFiberEquiv g) ⟨a,i⟩)) =
          (a.val, 0, cascadeShapeLeaves n (ss a) (ee a i)) := by
      simp only [E, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.sigmaCongrRight_apply, s, cascadeShapeLeaves_ofFn]
    rw [hE, hE]
    change indexedCommonDepth (n + 1) (xs i.val) (xs j.val) = _
    by_cases hab : a = b
    · subst b
      have hij : (xs i.val).1 = (xs j.val).1 ∧ (xs i.val).2.1 = (xs j.val).2.1 :=
        (hroot i.val j.val).mp (i.property.trans j.property.symm)
      simp only [indexedCommonDepth, ite_eq_left hij, and_self, ↓reduceIte]
      exact congrArg Fin.succ (he a i j)
    · have hij : ¬ ((xs i.val).1 = (xs j.val).1 ∧ (xs i.val).2.1 = (xs j.val).2.1) := by
        intro hij
        exact hab (i.property.symm.trans ((hroot i.val j.val).mpr hij) |>.trans j.property)
      have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp only [indexedCommonDepth, ite_eq_right hij, habv, false_and, ↓reduceIte]

end SphericalPerceptronFreeEnergy

end

end OAI
