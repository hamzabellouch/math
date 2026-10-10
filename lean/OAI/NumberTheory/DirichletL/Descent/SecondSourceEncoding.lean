import OAI.NumberTheory.DirichletL.Descent.CubeSource

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end SevenEighths.InverseMoment

end OAI
