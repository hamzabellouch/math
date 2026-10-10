import OAI.Computability.WLIdentification.AcceptingMates

namespace OAI

namespace WLIdentification

namespace ComparisonSchemas
variable {r : ℕ} {P E : Type} (S : ComparisonSchemas r P E)

/-- Exactly the individual scalar-image hypotheses of special-twist
sufficiency. No simultaneous choice satisfying the wires is required. -/
structure SpecialImages (b : E → Bit) where
  values : (p : P) → (Fin r → Bool) → Set (Fin (S.dimension p) → Bit)
  nonempty : ∀ p a, (values p a).Nonempty
  equation : ∀ e (a : S.DomainAddress e),
    S.left e '' values (S.source e) (S.expressAddress e true a) =
    (fun v => b e + S.right e v) '' values (S.target e) (S.expressAddress e false a)

namespace SpecialImages
variable {S} {b : E → Bit} (I : S.SpecialImages b)

theorem chooseAt (A : Fin r → Bool) (p : P) (v : Fin (S.dimension p) → Bit)
    (hv : v ∈ I.values p A) :
    ∃ q : S.RealShift, (∀ p, q p ∈ I.values p A) ∧ q p = v := by
  classical
  choose q hq using fun p => I.nonempty p A
  refine ⟨Function.update q p v, ?_, by simp⟩
  intro p'
  by_cases hp : p' = p
  · subst p'; simpa using hv
  · simpa only [Function.update_of_ne hp] using hq p'

theorem scalar_mem (e : E) (a : S.DomainAddress e) (side : Bool) (q : S.RealShift)
    (hq : ∀ p, q p ∈ I.values p (S.expressAddress e side a)) :
    (if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) ∈
      S.left e '' I.values (S.source e) (S.expressAddress e true a) := by
  cases side with
  | false =>
    rw [I.equation]
    exact ⟨q (S.target e), hq _, rfl⟩
  | true => exact ⟨q (S.source e), hq _, rfl⟩

theorem scalar_preimage (e : E) (a : S.DomainAddress e) (side : Bool) (s : Bit)
    (hs : s ∈ S.left e '' I.values (S.source e) (S.expressAddress e true a)) :
    ∃ q : S.RealShift, (∀ p, q p ∈ I.values p (S.expressAddress e side a)) ∧
      (if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))) = s := by
  cases side with
  | false =>
    rw [I.equation] at hs
    obtain ⟨v, hv, he⟩ := hs
    obtain ⟨q, hq, eq⟩ := I.chooseAt _ _ v hv
    refine ⟨q, hq, ?_⟩
    change b e + S.right e (q (S.target e)) = s
    rw [eq]
    exact he
  | true =>
    obtain ⟨v, hv, he⟩ := hs
    obtain ⟨q, hq, eq⟩ := I.chooseAt _ _ v hv
    refine ⟨q, hq, ?_⟩
    change S.left e (q (S.source e)) = s
    rw [eq]
    exact he

/-- The one constrained old wrapping component lifts even if it lies entirely
inside a wire and the new cut re-expresses it at the opposite real endpoint. -/
theorem wrapping_shift_extension {n : ℕ} (hr : 3 ≤ r) {U : Finset (S.layout n).Block}
    (hu : U.card ≤ r) (hw : (S.layout n).Wrapping (by omega) U)
    {cut cut' : E → Fin n} (hc : S.Avoids n U cut) (hc' : S.Avoids n U cut')
    {A A' : Fin r → Bool}
    (hA : (S.layout n).IsWrappingAddress U (S.align n cut) A)
    (hA' : (S.layout n).IsWrappingAddress U (S.align n cut') A')
    (q : S.RealShift) (hq : ∀ p, q p ∈ I.values p A) :
    ∃ q' : S.RealShift, (∀ p, q' p ∈ I.values p A') ∧
      ∀ h : (S.layout n).HName, Sum.inl h ∈ (S.layout n).names U →
        S.starShift n cut' b q' h.1 = S.starShift n cut b q h.1 := by
  classical
  have hpos : 0 < U.card := lt_of_lt_of_le (by omega) ((S.layout n).wrapping_card hr hw)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  let root := (S.layout n).blockRepresentative z
  have he (q' : S.RealShift) (l : S.Link n) (hl : l ∈ (S.layout n).usedLinks U) :
      (S.layout n).firstForm l (S.starShift n cut b q ((S.layout n).first l)) +
        (S.layout n).secondForm l (S.starShift n cut b q ((S.layout n).second l)) =
      (S.layout n).firstForm l (S.starShift n cut' b q' ((S.layout n).first l)) +
        (S.layout n).secondForm l (S.starShift n cut' b q' ((S.layout n).second l)) :=
    (S.starShift_link hc b q hl).trans (S.starShift_link hc' b q' hl).symm
  by_cases hre : ∃ (d : (S.layout n).Corner) (p : P),
      ((S.layout n).cornerGraph (by omega) U).Reachable root d ∧ d.1 = Sum.inl p
  · obtain ⟨d, p, hd, hdp⟩ := hre
    have hAA := S.wrapping_real_addresses hr hu hw hc hc' hA hA' hz hdp hd
    subst A'
    refine ⟨q, hq, ?_⟩
    intro h hh
    have hpath := hd.symm.trans ((S.layout n).wrapping_names_reachable hr hu hw hz hh).1
    have hbase : S.starShift n cut b q d.1 = S.starShift n cut' b q d.1 := by rw [hdp]; rfl
    exact (S.shift_agreement_reachable (by omega) _ _ (he q)
      (fun _ _ _ _ => rfl) hbase hpath).symm
  · have hn : S.NoRealFrom n (by omega) U root := by
      intro d hd p hp
      exact hre ⟨d, p, hd, hp⟩
    have htype : ∃ (e : E) (j : Fin (n + 1)), root.1 = Sum.inr (e, j) := by
      cases ht : root.1 with
      | inl p => exact (hn root (.refl root) p ht).elim
      | inr ej => exact ⟨ej.1, ej.2, rfl⟩
    obtain ⟨e, j, ht⟩ := htype
    let side := decide (S.onLeft n cut e j)
    let side' := decide (S.onLeft n cut' e j)
    have harm : S.arm n cut root.1 = some (e, side) := by rw [ht]; rfl
    have harm' : S.arm n cut' root.1 = some (e, side') := by rw [ht]; rfl
    obtain ⟨a, hAa, hAa'⟩ := S.wrapping_internal_addresses hr hu hw hc hc' hA hA' hz hn harm harm'
    let scalar : Bit := if side then S.left e (q (S.source e)) else b e + S.right e (q (S.target e))
    have hs := I.scalar_mem e a side q (by simpa only [← hAa] using hq)
    obtain ⟨q', hq', hscalar⟩ := I.scalar_preimage e a side' scalar hs
    refine ⟨q', by simpa only [← hAa'] using hq', ?_⟩
    intro h hh
    have hpath := ((S.layout n).wrapping_names_reachable hr hu hw hz hh).1
    have hbase : S.starShift n cut b q root.1 = S.starShift n cut' b q' root.1 := by
      rw [ht]
      funext k
      change (if S.onLeft n cut e j then _ else _) = (if S.onLeft n cut' e j then _ else _)
      simpa only [scalar, side, side', decide_eq_true_eq] using hscalar.symm
    exact (S.shift_agreement_reachable (by omega) _ _ (he q')
      (fun d hd p hp => (hn d hd p hp).elim) hbase hpath).symm

end SpecialImages
end ComparisonSchemas

namespace RingLayout
variable {r : ℕ} {T L : Type} (R : RingLayout r T L)

theorem translation_eq_of_shifts {U : Finset R.Block} (old new : R.Shift) (M : R.Potential)
    (he : ∀ h : R.HName, Sum.inl h ∈ R.names U → new h.1 = old h.1)
    {b : R.Block} (hb : b ∈ U) {c : R.Coordinate} (hc : c ∈ R.coordinates b) :
    R.translation new M c = R.translation old M c := by
  have hn := R.name_present hb (R.coordinate_name_mem hc)
  cases c with
  | inl h =>
    change (R.potentialHorizontal new M h.1) h.2 = (R.potentialHorizontal old M h.1) h.2
    unfold potentialHorizontal
    rw [he h.1 hn]
  | inr v => rfl

end RingLayout

namespace ComparisonSchemas.SpecialImages
variable {r : ℕ} {P E : Type} {S : ComparisonSchemas r P E} {b : E → Bit}
    (I : S.SpecialImages b)

/-- A stronger sufficient family using globally completed cut stars. Its
address restriction is imposed only by wrapping subcollections of size r. -/
def Admissible (n : ℕ) (hr : 2 ≤ r) (U : Finset (S.layout n).Block)
    (x : (S.layout n).Coordinate → Bit) : Prop :=
  U.card ≤ r + 1 ∧ ∃ cut : E → Fin n, S.Avoids n U cut ∧
    ∃ A : Fin r → Bool, S.GoodAddress n hr U cut A ∧
      ∃ q : S.RealShift, (∀ p, q p ∈ I.values p A) ∧
        ∃ M : (S.layout n).Potential, ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a,
          x c = (S.layout n).translation (S.starShift n cut b q) M c

theorem admissible_nonempty {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n)
    (U : Finset (S.layout n).Block) (hu : U.card ≤ r + 1) :
    ∃ x, I.Admissible n (by omega) U x := by
  classical
  obtain ⟨cut, hc⟩ := S.exists_cuts n U (lt_of_le_of_lt hu hn)
  obtain ⟨A, hA⟩ := S.goodAddress_exists n hr hu hc
  choose q hq using fun p => I.nonempty p A
  refine ⟨(S.layout n).translation (S.starShift n cut b q) (fun _ _ => 0),
    hu, cut, hc, A, hA, q, hq, (fun _ _ => 0), ?_⟩
  exact fun _ _ _ _ => rfl

theorem admissible_restrict {n : ℕ} {hr : 2 ≤ r} {U V : Finset (S.layout n).Block}
    {x : (S.layout n).Coordinate → Bit} (hVU : V ⊆ U) (hx : I.Admissible n hr U x) :
    I.Admissible n hr V x := by
  obtain ⟨hu, cut, hc, A, hA, q, hq, M, hM⟩ := hx
  exact ⟨(Finset.card_le_card hVU).trans hu, cut, S.avoids_mono hVU hc,
    A, S.goodAddress_mono hVU hA, q, hq, M, fun a ha => hM a (hVU ha)⟩

variable [Fintype P] [Fintype E]

theorem admissible_legal {n : ℕ} {hr : 2 ≤ r} {U : Finset (S.layout n).Block}
    {x : (S.layout n).Coordinate → Bit} (hx : I.Admissible n hr U x)
    {a : (S.layout n).Block} (ha : a ∈ U) :
    ((S.layout n).affine hr).Legal (S.specialTwist n b) a (((S.layout n).affine hr).restrict a x) := by
  obtain ⟨_, cut, hc, _, _, q, _, M, hM⟩ := hx
  have he : ((S.layout n).affine hr).restrict a x =
      ((S.layout n).affine hr).restrict a ((S.layout n).translation (S.starShift n cut b q) M) := by
    funext c
    exact hM a ha c.val c.property
  rw [he]
  exact S.translation_legal hc hr b q M ha

omit [Fintype P] [Fintype E] in
theorem admissible_extend {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n)
    {U : Finset (S.layout n).Block} {x : (S.layout n).Coordinate → Bit}
    (hu : U.card < r + 1) (hx : I.Admissible n (by omega) U x) (z : (S.layout n).Block) :
    ∃ y, I.Admissible n (by omega) (insert z U) y ∧
      ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
  classical
  obtain ⟨_, cut, hc, A, hA, q, hq, M, hM⟩ := hx
  have hu' : U.card ≤ r := by omega
  have hnew : (insert z U).card ≤ r + 1 := by
    have := Finset.card_insert_le z U
    omega
  obtain ⟨cut', hc'⟩ := S.exists_cuts n (insert z U) (lt_of_le_of_lt hnew hn)
  obtain ⟨A', hA'⟩ := S.goodAddress_exists n hr hnew hc'
  have hsub : U ⊆ insert z U := Finset.subset_insert _ _
  have hc'U := S.avoids_mono hsub hc'
  have finish (q' : S.RealShift) (hq' : ∀ p, q' p ∈ I.values p A')
      (N : (S.layout n).Potential)
      (hN : ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a,
        (S.layout n).translation (S.starShift n cut' b q') N c =
          (S.layout n).translation (S.starShift n cut b q) M c) :
      ∃ y, I.Admissible n (by omega) (insert z U) y ∧
        ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
    refine ⟨(S.layout n).translation (S.starShift n cut' b q') N,
      ⟨hnew, cut', hc', A', hA', q', hq', N, fun _ _ _ _ => rfl⟩, ?_⟩
    intro a ha c hc
    exact (hN a ha c hc).trans (hM a ha c hc).symm
  by_cases hw : (S.layout n).Wrapping (by omega) U
  · obtain ⟨q', hq', hshift⟩ := I.wrapping_shift_extension hr hu' hw hc hc'U
      (hA U (Finset.Subset.refl _) hu' hw) (hA' U hsub hu' hw) q hq
    apply finish q' hq' M
    intro a ha c hc
    exact (S.layout n).translation_eq_of_shifts _ _ M hshift ha hc
  · choose q' hq' using fun p => I.nonempty p A'
    obtain ⟨N, hN⟩ := (S.layout n).adjust_potential hr hw (S.starShift n cut b q)
      (S.starShift n cut' b q') M (fun l hl =>
        (S.starShift_link hc b q hl).trans (S.starShift_link hc'U b q' hl).symm)
    exact finish q' hq' N hN

/-- A proved producer of the exact-projection interface, not a hypothesis
asserting that local translations happen to extend. -/
noncomputable def offsetFamily {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n) :
    ((S.layout n).affine (by omega)).OffsetFamily (S.specialTwist n b) (r + 1) where
  admissible := I.Admissible n (by omega)
  empty := I.admissible_nonempty hr hn ∅ (by simp)
  legal := fun hx _ ha => I.admissible_legal hx ha
  restrict := I.admissible_restrict
  extend := I.admissible_extend hr hn

include I in
/-- Equivalence of the special twist on the uncolored
leaf-coded graph; the private interior may be arbitrarily longer than K. -/
theorem equivalent_special {n : ℕ} (hr : 32 ≤ r) (hn : r + 1 < n) :
    Equivalent r (((S.layout n).affine (by omega)).graph 0)
      (((S.layout n).affine (by omega)).graph (S.specialTwist n b)) := by
  exact AffineBlocks.graph_equivalent_of_offsetFamily _ (S.layout n).owner
    (S.layout n).owner_covers (S.specialTwist n b) (offsetFamily I (by omega) hn)
    (by omega) (by omega)

end ComparisonSchemas.SpecialImages

end WLIdentification

end OAI
