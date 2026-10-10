import OAI.ModelTheory.Categoricity.AEC

namespace OAI

/-!
# A CH obstruction to a prescribed categoricity threshold

Under CH, a countable relational language admits an abstract elementary class
with least Löwenheim–Skolem number `aleph0`, two nonisomorphic models of size
`beth (omega 2) = hanf aleph0`, and categoricity, including existence, at every
cardinal at least `tailThreshold`. Distinct base cardinalities separate the
endpoint models, while finite-support row and column translations establish
the included categoricity tail.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples

variable (hCH : CH.{u})

namespace Existence

abbrev RationalBase := ULift.{u} ℚ

instance : DenselyOrdered RationalBase.{u} where
  dense a b h := by
    obtain ⟨c, hc, hd⟩ := exists_between (show a.down < b.down from h)
    exact ⟨⟨c⟩, hc, hd⟩

instance : NoMinOrder RationalBase.{u} where
  exists_lt a := by
    obtain ⟨b, hb⟩ := exists_lt a.down
    exact ⟨⟨b⟩, hb⟩

instance : NoMaxOrder RationalBase.{u} where
  exists_gt a := by
    obtain ⟨b, hb⟩ := exists_gt a.down
    exact ⟨⟨b⟩, hb⟩

def countableData (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Data.{u} where
  I := μ.ord.ToType
  B := RationalBase
  indexNonempty := by
    have : Infinite μ.ord.ToType := Cardinal.aleph0_le_mk_iff.1 (by simpa using hμ)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable _ _ := Set.to_countable _
  bits _ _ _ := false

theorem countableData_object (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    (countableData μ hμ).IsObject hCH := by
  have : Countable (countableData μ hμ).B := by change Countable RationalBase; infer_instance
  exact Data.countable_object _ _

theorem countableData_index (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).I = μ := by
  change #μ.ord.ToType = μ
  simp only [Cardinal.mk_toType, Cardinal.card_ord]

theorem countableData_cardinal (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).Carrier = μ := by
  rw [Data.cardinal_eq, countableData_index]
  change max (max μ #RationalBase.{u}) ℵ₀ = μ
  rw [max_eq_left ((Cardinal.mk_le_aleph0 (α := RationalBase.{u})).trans hμ), max_eq_left hμ]

theorem models (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ R, AEC.Object (hCH := hCH) R ∧ R.carrier.card = μ := by
  refine ⟨Coding.coded (countableData μ hμ),
    ⟨Coding.codedPresentation _, countableData_object hCH μ hμ⟩, ?_⟩
  rw [Coding.coded_cardinal, countableData_cardinal]

end Existence

namespace Categoricity

theorem aleph_one_lt : (ℵ_ 1 : Cardinal.{u}) < tailThreshold.{u} :=
  (Cardinal.cantor _).trans ThresholdArithmetic.palette_lt

theorem index_eq (M : Data.{u}) {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ)
    (hM : #M.Carrier = μ) : #M.I = μ := by
  have hi : #M.I ≤ μ := (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h)).trans_eq hM
  apply le_antisymm hi
  by_contra! hn
  have hb : #M.B < μ := M.base_bound.trans_lt (aleph_one_lt.trans_le hμ)
  have hz : ℵ₀ < μ := (Cardinal.aleph0_le_aleph 1).trans_lt (aleph_one_lt.trans_le hμ)
  have hc := max_lt (max_lt hn hb) hz
  rw [← M.cardinal_eq, hM] at hc
  exact hc.false

theorem countable (M : Data.{u}) (hCH : CH.{u}) (ho : M.IsObject hCH)
    {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ) (hM : #M.Carrier = μ) : Countable M.B := by
  by_contra hn
  have hh := M.uncountable_index_bound hCH ho hn
  rw [index_eq M hμ hM] at hh
  exact hh.not_ge hμ

theorem tail (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : tailThreshold.{u} ≤ μ) :
    (classData hCH).Categorical μ := by
  refine ⟨Existence.models hCH μ
    ((Cardinal.aleph0_le_aleph 1).trans (aleph_one_lt.le.trans hμ)), ?_⟩
  intro R T hr ht hc hd
  obtain ⟨P, hp⟩ := hr
  obtain ⟨Q, hq⟩ := ht
  have hpc : #P.data.Carrier = μ := (Coding.cardinal P.equiv).trans hc
  have hqc : #Q.data.Carrier = μ := (Coding.cardinal Q.equiv).trans hd
  have := countable P.data hCH hp hμ hpc
  have := countable Q.data hCH hq hμ hqc
  obtain ⟨f, hi, hb⟩ := countable_isomorphic
    ((index_eq P.data hμ hpc).trans (index_eq Q.data hμ hqc).symm)
  exact ⟨P.isoOfMap Q f (f.surjective hi hb)⟩

end Categoricity

namespace EndpointModels

open Diagrams
open Existence

abbrev Base := Tag.{u} ×ₗ RationalBase.{u}

instance tag_nonempty : Nonempty Tag.{u} := Ordinal.nonempty_toType_iff.2 (Ordinal.omega_pos 1).ne'

theorem tag_initial_countable (b : Tag.{u}) : (Set.Iic b).Countable := by
  have : Countable (Set.Iio b) := by
    apply Cardinal.mk_le_aleph0_iff.1
    apply Cardinal.lt_aleph_one_iff.1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.mk_Iio_lt b (by simp [Tag]))
  have h : Set.Iic b = insert b (Set.Iio b) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_Iio, le_iff_eq_or_lt]
  rw [h]
  exact (Set.to_countable (Set.Iio b)).insert b

theorem locallyCountable (a b : Base.{u}) : (Set.Icc a b).Countable := by
  have := (tag_initial_countable (ofLex b).1).to_subtype
  let f : Set.Icc a b → Set.Iic (ofLex b).1 × RationalBase.{u} :=
    fun x => (⟨(ofLex x.val).1, Prod.Lex.monotone_fst _ _ x.property.2⟩, (ofLex x.val).2)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.1.val) h)
      (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.2) h)
  exact Set.countable_coe_iff.1 hf.countable

theorem base_cardinal : #Base.{u} = (ℵ_ 1 : Cardinal.{u}) := by
  rw [Cardinal.mk_congr (ofLex : Base.{u} ≃ _), Cardinal.mk_prod]
  simp [Tag, RationalBase]

def baseEquiv : Base.{u} ≃ Tag.{u} := Classical.choice (Cardinal.eq.1 (by
  rw [base_cardinal, Cardinal.mk_toType, Ordinal.card_omega]))

theorem endpoint_infinite : ℵ₀ ≤ endpoint.{u} := Cardinal.aleph0_le_beth _

theorem base_le_endpoint : (ℵ_ 1 : Cardinal.{u}) ≤ endpoint.{u} := by
  apply (Cardinal.aleph.monotone (by norm_num : (1 : Ordinal.{u}) ≤ 2)).trans
  change ℵ_ 2 ≤ beth (ω_ 2)
  rw [← Cardinal.ord_aleph]
  exact Cardinal.le_beth_ord _

def data (hCH : CH.{u}) : Data.{u} where
  I := EndpointDiagrams.D
  B := Base
  indexNonempty := by
    have : Infinite EndpointDiagrams.D.{u} := Cardinal.aleph0_le_mk_iff.1
      (EndpointDiagrams.cardinal.symm ▸ endpoint_infinite)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable := locallyCountable
  bits t n b := Colors.representative (EndpointDiagrams.colors hCH t (baseEquiv b)).down n

theorem data_colors (hCH : CH.{u}) (t : Tuples.Tuple EndpointDiagrams.D.{u}) (b : Base.{u}) :
    (data hCH).colors t b = EndpointDiagrams.colors hCH t (baseEquiv b) := by
  apply ULift.ext
  exact Colors.representative_color _

theorem object (hCH : CH.{u}) : (data hCH).IsObject hCH := by
  intro t
  have h := (EndpointDiagrams.countable_failures hCH t).preimage baseEquiv.injective
  apply h.mono
  intro b hb ht
  apply hb
  apply (Tests.congr hCH t (fun _ _ => data_colors hCH _ b)).mpr ht

theorem cardinal (hCH : CH.{u}) : #(data hCH).Carrier = endpoint.{u} := by
  rw [Data.cardinal_eq]
  change max (max #EndpointDiagrams.D.{u} #Base.{u}) ℵ₀ = endpoint.{u}
  rw [EndpointDiagrams.cardinal, base_cardinal, max_eq_left base_le_endpoint,
    max_eq_left endpoint_infinite]

theorem twoModels (hCH : CH.{u}) : (classData hCH).TwoModels endpoint.{u} := by
  let M := countableData endpoint endpoint_infinite
  let N := data hCH
  let P := Coding.codedPresentation M
  let Q := Coding.codedPresentation N
  refine ⟨Coding.coded M, Coding.coded N,
    ⟨P, countableData_object hCH endpoint endpoint_infinite⟩, ⟨Q, object hCH⟩, ?_, ?_, ?_⟩
  · rw [Coding.coded_cardinal]
    exact countableData_cardinal endpoint endpoint_infinite
  · rw [Coding.coded_cardinal]
    exact cardinal hCH
  · rintro ⟨e⟩
    let f := (P.transport e).comparison Q
    have : Countable (P.transport e).data.B := by change Countable RationalBase; infer_instance
    have : Countable N.B := f.base_surjective.countable
    have hc := Cardinal.mk_le_aleph0 (α := N.B)
    change #Base.{u} ≤ ℵ₀ at hc
    rw [base_cardinal] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal.{u}) < 1)).not_ge hc

end EndpointModels

end Arrays

theorem main (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ := by
  refine ⟨Arrays.Language, Arrays.language_countable, Arrays.classData hCH,
    Arrays.AEC.isAEC, Arrays.AEC.hasLSNumber, ThresholdArithmetic.endpoint_eq_hanf hCH,
    Arrays.EndpointModels.twoModels hCH, Arrays.Categoricity.tail hCH⟩

theorem endpoint_lt_tailThreshold : endpoint.{u} < tailThreshold.{u} := by
  apply Cardinal.beth_strictMono
  rw [← Cardinal.ord_aleph]
  apply Cardinal.ord_strictMono
  have hs : (ℵ_ (2 : Ordinal.{u})) = succ (ℵ_ (1 : Ordinal.{u})) := by
    rw [Cardinal.succ_aleph]
    norm_num
  apply lt_of_le_of_lt _ (lt_succ _)
  rw [hs]
  exact Order.succ_le_of_lt (Cardinal.cantor _)

theorem prescribed_transfer_fails (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        hanf (ℵ₀ : Cardinal.{u}) < succ tailThreshold ∧
        K.Categorical (succ tailThreshold) ∧ ¬ K.Categorical (hanf ℵ₀) := by
  obtain ⟨L, hL, K, hK, hLS, he, ht, hc⟩ := main hCH
  refine ⟨L, hL, K, hK, hLS, ?_, hc _ (le_succ _), ?_⟩
  · rw [← he]
    exact endpoint_lt_tailThreshold.trans (lt_succ _)
  · rw [← he]
    obtain ⟨M, N, hm, hn, hmc, hnc, hne⟩ := ht
    exact fun h => hne (h.2 M N hm hn hmc hnc)

end CHObstruction

end

end OAI
