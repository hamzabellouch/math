import OAI.Analysis.PureInfiniteness.CentralSequenceAbsorption
import OAI.Analysis.WeakInfiniteness.CentralExactPair
import OAI.Analysis.WeakInfiniteness.UnitalCuntzEmbedding

namespace OAI

/-! # Multiplicative central Cuntz maps from relative local isometries

The relations are imposed after multiplication by the original algebra.
Passing to the annihilator quotient gives genuine Cuntz isometries, not cpc
images of such isometries.
-/

noncomputable section
open Filter Topology
open scoped ENNReal TensorProduct

namespace WeakPureInfiniteness

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "C" => NonunitalGamma.normCentralizer (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "q" => NonunitalGamma.centralSequenceQuotient (A := A) U

omit [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
  [Fact ((U : Filter ℕ) ≤ atTop)] in
lemma centralQuotient_eq_of_right (x y : C)
    (h : ∀ a : A, ((x : N) - (y : N)) * ι a = 0) : q x = q y := by
  apply (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff _ _ _).mpr
  intro a
  refine ⟨h a, ?_⟩
  have hc := (x - y).property a
  change ((x : N) - (y : N)) * ι a = ι a * ((x : N) - (y : N)) at hc
  exact hc.symm.trans (h a)

lemma centralCuntzPair_of_relative (s t : C)
    (hs : ∀ a : A, star (s : N) * s * ι a = ι a)
    (ht : ∀ a : A, star (t : N) * t * ι a = ι a)
    (hst : ∀ a : A, star (s : N) * t * ι a = 0) :
    star (q s) * q s = 1 ∧ star (q t) * q t = 1 ∧ star (q s) * q t = 0 := by
  have hi (z : C) (hz : ∀ a : A, star (z : N) * z * ι a = ι a) :
      star (q z) * q z = 1 := by
    rw [← map_star, ← map_mul]
    change q (star z * z) = q (NonunitalGamma.centralLocalUnit U)
    apply centralQuotient_eq_of_right
    intro a
    change (star (z : N) * z - (NonunitalGamma.centralLocalUnit (A := A) U).val) * ι a = 0
    rw [sub_mul, hz, NonunitalGamma.centralLocalUnit_mul, sub_self]
  refine ⟨hi s hs, hi t ht, ?_⟩
  rw [← map_star, ← map_mul, ← map_zero q]
  apply centralQuotient_eq_of_right
  intro a
  change (star (s : N) * t - 0) * ι a = 0
  simpa only [sub_zero] using hst a

private def relativePairTest (a : ℕ → A) (j : Fin 5 × ℕ) (x : Fin 2 → A) : ℝ :=
  match j.1.val with
  | 0 => ‖a j.2 * x 0 - x 0 * a j.2‖
  | 1 => ‖a j.2 * x 1 - x 1 * a j.2‖
  | 2 => ‖star (x 0) * x 0 * a j.2 - a j.2‖
  | 3 => ‖star (x 1) * x 1 * a j.2 - a j.2‖
  | _ => ‖star (x 0) * x 1 * a j.2‖

omit [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] in
private lemma relativePairTest_nonneg (a : ℕ → A) (j : Fin 5 × ℕ) (x : Fin 2 → A) :
    0 ≤ relativePairTest a j x := by
  rcases j with ⟨j, n⟩
  fin_cases j <;> exact norm_nonneg _

omit [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] in
private lemma relativePairTest_supply (a : ℕ → A) (h : LocalCentralCuntzPair A)
    (F : Finset (Fin 5 × ℕ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Fin 2 → A, (∀ i, ‖x i‖ ≤ 1) ∧
      ∀ j ∈ F, relativePairTest a j x < ε := by
  classical
  obtain ⟨s, t, hs, ht, he⟩ := h (F.image (fun j => a j.2)) ε hε
  let x : Fin 2 → A := ![s, t]
  refine ⟨x, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hs
    · exact ht
  · rintro ⟨j, n⟩ hj
    have hn := he (a n) (Finset.mem_image.mpr ⟨(j, n), hj, rfl⟩)
    fin_cases j
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2.1
    · exact hn.2.2.2.1
    · exact hn.2.2.2.2

/-- Local relative Cuntz relations produce an actual unital central map. -/
theorem centralOInfinityMap_of_localCuntzPair (h : LocalCentralCuntzPair A) :
    Nonempty (OInfinity →⋆ₐ[ℂ] NonunitalGamma.CentralSequenceAlgebra (A := A) U) := by
  classical
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq A
  let F (k : ℕ) : Finset (Fin 5 × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  have hsupply (k : ℕ) := relativePairTest_supply a h (F k)
    (show 0 < 1 / ((k : ℝ) + 1) by positivity)
  choose v hvn hv using hsupply
  let x : Fin 2 → lp (fun _ : ℕ => A) ∞ := fun i =>
    ⟨fun k => v k i, memℓp_infty ⟨1, by
      rintro _ ⟨k, rfl⟩
      exact hvn k i⟩⟩
  have hx (j : Fin 5 × ℕ) :
      Tendsto (fun k => relativePairTest a j (fun i => x i k))
        (U : Filter ℕ) (𝓝 0) := by
    apply Filter.Tendsto.mono_left _ (Fact.out : (U : Filter ℕ) ≤ atTop)
    apply squeeze_zero' (Eventually.of_forall fun _ => relativePairTest_nonneg a j _)
      _ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop j.2] with k hk
    exact (hv k j (by simp only [F, Finset.mem_product, Finset.mem_univ,
      true_and, Finset.mem_range]; omega)).le
  let z : Fin 2 → N := fun i => NormUltra.QuotientAlgebra.mk U (x i)
  have hc (i : Fin 2) : z i ∈ C := by
    have he (n : ℕ) : z i * ι (a n) = ι (a n) * z i := by
      have hh : Tendsto (fun k => ‖a n * x i k - x i k * a n‖)
          (U : Filter ℕ) (𝓝 0) := by
        fin_cases i
        · exact hx (0, n)
        · exact hx (1, n)
      have eq := (NormUltra.QuotientAlgebra.mk_eq_mk_iff
        (NonunitalGamma.boundedConstant (A := A) (a n) * x i)
        (x i * NonunitalGamma.boundedConstant (A := A) (a n))).mpr hh
      exact eq.symm
    intro b
    exact ha.induction_on b
      (isClosed_eq (continuous_const.mul (map_continuous ι))
        ((map_continuous ι).mul continuous_const)) he
  let S : C := ⟨z 0, hc 0⟩
  let T : C := ⟨z 1, hc 1⟩
  have hi (i : Fin 2) (b : A) : star (z i) * z i * ι b = ι b := by
    refine ha.induction_on b
      (isClosed_eq (continuous_const.mul (map_continuous ι)) (map_continuous ι)) ?_
    intro n
    have hh : Tendsto (fun k => ‖star (x i k) * x i k * a n - a n‖)
        (U : Filter ℕ) (𝓝 0) := by
      fin_cases i
      · exact hx (2, n)
      · exact hx (3, n)
    exact (NormUltra.QuotientAlgebra.mk_eq_mk_iff
      (star (x i) * x i * NonunitalGamma.boundedConstant (A := A) (a n))
      (NonunitalGamma.boundedConstant (A := A) (a n))).mpr hh
  have hij (b : A) : star (z 0) * z 1 * ι b = 0 := by
    refine ha.induction_on b
      (isClosed_eq (continuous_const.mul (map_continuous ι)) continuous_const) ?_
    intro n
    have hh : Tendsto (fun k => ‖star (x 0 k) * x 1 k * a n - (0 : A)‖)
        (U : Filter ℕ) (𝓝 0) := by
      simpa [relativePairTest] using hx (4, n)
    exact (NormUltra.QuotientAlgebra.mk_eq_mk_iff
      (star (x 0) * x 1 * NonunitalGamma.boundedConstant (A := A) (a n)) 0).mpr hh
  obtain ⟨hs, ht, hst⟩ := centralCuntzPair_of_relative U S T (hi 0) (hi 1) hij
  exact ⟨oInfinityMap (fun n => (q T)^n * q S)
    (binaryCuntzFamily_relations hs ht hst)⟩

theorem centralOInfinityMap_of_identityDiagonalization
    (h : ContractiveIdentityDiagonalization A) :
    Nonempty (OInfinity →⋆ₐ[ℂ] NonunitalGamma.CentralSequenceAlgebra (A := A) U) :=
  centralOInfinityMap_of_localCuntzPair U h.localCentralCuntzPair

include U in
/-- The local multiplicative witnesses suffice for nonunital absorption once
the published structural facts about `OInfinity` are supplied. -/
theorem absorbsOInfinity_of_localCuntzPair
    (h : LocalCentralCuntzPair A)
    (hD : Pureness.IsNuclear.{1,1} OInfinity)
    (hs : Pureness.TopologicallySimple OInfinity)
    {T : Type*} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f) :
    AbsorbsOInfinity A := by
  cases subsingleton_or_nontrivial A with
  | inl hA =>
    let := hA
    exact absorbsOInfinity_of_subsingleton A
  | inr hA =>
    let := hA
    obtain ⟨φ⟩ := centralOInfinityMap_of_localCuntzPair U h
    exact minimalTensor_equiv_of_central_embedding U φ hD hs f hf hd hh

end WeakPureInfiniteness

end

end OAI
