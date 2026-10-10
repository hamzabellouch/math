import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LitEdgesEmptyOfNo

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma single_edge_weight (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index) (e : Fin ℓ) :
    subtreeUnionWeight w p {e} = S.amplitude p *
      S.beta p ^ (w.children (w.offset e.castSucc) + w.children (w.offset e.succ)) := by
  rw [subtreeUnionWeight]
  simp only [card_singleton, pow_one, edgeVertices, image_singleton]
  rw [prod_union (disjoint_singleton.mpr (w.endpoints_ne hh e)), prod_singleton,
    prod_singleton, pow_add]

def singletonIsTagged (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (e : Fin ℓ) : Prop :=
  (p : ℕ) ∈ listSupport w 𝔏 ∨ ¬ w.Uncorrupted (p : ℕ) e

def singletonTokenWeight (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (e : Fin ℓ) : ℝ :=
  if singletonIsTagged w 𝔏 p e then 2 else
    if w.Good e then theta / 2 else subtreeUnionWeight w p {e} + theta

lemma singletonTokenWeight_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (e : Fin ℓ) : 0 ≤ singletonTokenWeight w 𝔏 p e := by
  unfold singletonTokenWeight
  split_ifs
  · norm_num
  · norm_num
  · exact add_nonneg (subtreeUnionWeight_nonneg w p _) (by norm_num)

theorem free_center_tree_mean (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FreeCenterIndex w)
    (e : Fin ℓ) (he : (p.val.val : ℕ) ∣ w.label e)
    (hlarge : 2 * (ℓ+1) ≤ (p.val.val : ℕ)) :
    |avg (localWithList w 𝔏 p.val.val)| ≤ singletonTokenWeight w 𝔏 p.val.val e / (p.val.val : ℝ) := by
  unfold singletonTokenWeight
  split_ifs with ht hg
  · exact tagged_free_center_mean w 𝔏 p e he
  · have hlist : (p.val.val : ℕ) ∉ listSupport w 𝔏 := fun h => ht (Or.inl h)
    have hunc : w.Uncorrupted (p.val.val : ℕ) e := by
      by_contra hn
      exact ht (Or.inr hn)
    convert (good_free_center_mean w hh 𝔏 p e he hg hunc hlist hlarge).2 using 1
    field_simp
  · have hweight : subtreeUnionWeight w p.val.val {e} =
        betaZ ^ (w.children (w.offset e.castSucc) + w.children (w.offset e.succ)) := by
      rw [single_edge_weight w hh p.val.val e, beta_eq_center p.val.val p.property]
      simp only [amplitude, p.property, ite_false, one_mul]
    rw [hweight]
    exact nongood_free_center_mean w hh 𝔏 p e he

def fixedTreeWeight (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) : ℝ :=
  subtreeUnionWeight w p E * 2 ^ ((treeOccurrences w p) \ E).card

lemma fixedTreeWeight_nonneg (w : ClosedLine h ℓ) (p : S.Index) (E : Finset (Fin ℓ)) :
    0 ≤ fixedTreeWeight w p E :=
  mul_nonneg (subtreeUnionWeight_nonneg w p E) (pow_nonneg (by norm_num) _)

theorem fixed_tree_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index) (E : Finset (Fin ℓ))
    (htop : NoComponentTop w U p E) (hocc : (treeOccurrences w p).Nonempty) :
    avg (recordPrime w 𝔏 U p E) ≤ fixedTreeWeight w p E / (p : ℝ) := by
  have htwo : (1 : ℝ) ≤ 2 ^ ((treeOccurrences w p) \ E).card := one_le_pow₀ (by norm_num)
  have hweight : subtreeUnionWeight w p E ≤ fixedTreeWeight w p E :=
    le_mul_of_one_le_right (subtreeUnionWeight_nonneg w p E) htwo
  rcases eq_empty_or_nonempty E with rfl | hE
  · have hh := fixed_unlit_tree_mean w 𝔏 U hU p hocc
    apply hh.trans
    rw [subtreeUnionWeight_empty] at hweight
    simpa only [one_div] using div_le_div_of_nonneg_right hweight (Nat.cast_nonneg (p : ℕ))
  · exact (fixed_lit_tree_mean w 𝔏 U hU p E htop hE).trans
      (div_le_div_of_nonneg_right hweight (Nat.cast_nonneg (p : ℕ)))

lemma recordPrime_le_charged_local (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (p : S.Index) (E : Finset (Fin ℓ)) (a : ZMod (p : ℕ)) :
    recordPrime w 𝔏 U p E a ≤ |localWithList w 𝔏 p a| * allPrimeCharges w U p a := by
  unfold recordPrime
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (abs_nonneg _) (allPrimeCharges_nonneg w U p a)

lemma no_tree_mean_le_one (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i) :
    avg (fun a => |localWithList w 𝔏 p a| * allPrimeCharges w U p a) ≤ 1 := by
  apply (avg_mono (g := fun _ => 1) ?_).trans_eq (avg_const _)
  intro a
  exact ((charged_local_le w 𝔏 U p a).trans (charged_prime_le_background w U hU p hnot a)).trans
    (backgroundMultiplier_bounds w U (fun v hv => (good_origin_data w (hU hv)).2.2.1) p a).2

def IsCollision (w : ClosedLine h ℓ) (p : S.Index) : Prop :=
  ¬ Set.InjOn (fun v : ℤ => (v : ZMod (p : ℕ))) (treeVertices w)

def backgroundExponent (w : ClosedLine h ℓ) (U : Finset ℤ) (p : S.Index) : ℝ :=
  -(treeDefect w p - (if S.IsCore p then betaC * (Real.exp kappa - 1) * U.card else 0)) / (p : ℝ)

def outsideTreeBound (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (p : S.Index) : ℝ :=
  if (p : ℕ) ∈ listSupport w 𝔏 then (p : ℝ)⁻¹ else
    if IsCollision w p then 1 else Real.exp (backgroundExponent w U p)

lemma outsideTreeBound_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (p : S.Index) : 0 ≤ outsideTreeBound w 𝔏 U p := by
  unfold outsideTreeBound
  split_ifs <;> positivity

theorem outside_tree_mean (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (p : S.Index)
    (hnot : ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i) :
    avg (fun a => |localWithList w 𝔏 p a| * allPrimeCharges w U p a) ≤ outsideTreeBound w 𝔏 U p := by
  unfold outsideTreeBound
  split_ifs with hl hc
  · exact list_no_tree_mean w 𝔏 U hU p hnot hl
  · exact no_tree_mean_le_one w 𝔏 U hU p hnot
  · exact background_kernel_mean w 𝔏 U hU p hnot (not_not.mp hc)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
