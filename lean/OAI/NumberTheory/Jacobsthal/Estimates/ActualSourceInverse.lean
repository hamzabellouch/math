import OAI.NumberTheory.Jacobsthal.Partitions.ActualBoxHarmonicInverse
import OAI.NumberTheory.Jacobsthal.Partitions.ActualBoxList

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def actualInverseException (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  witnessPairs (P.product Q) U (actualWitness Y small a delta V0 P S R Z cp)

theorem mem_actualInverseException (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) (p q u : ℕ) :
    ((p,q),u) ∈ actualInverseException Y small a delta V0 S R Z cp P Q U ↔
      p ∈ P ∧ q ∈ Q ∧ u ∈ U ∧ Nonstructured P (fun p => (a p : ℤ)) S R Z cp p q ∧
        WitnessingBadEdge Y small a delta V0 p q u := by
  constructor
  · intro hmem
    obtain ⟨hprod,hWitness⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hpq,hu⟩ := Finset.mem_product.mp hprod
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    exact ⟨hp,hq,hu,hWitness.1,hWitness.2⟩
  · rintro ⟨hp,hq,hu,hNon,hBad⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,hu⟩,⟨hNon,hBad⟩⟩

theorem actual_exception_weight (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) :
    (∑ t ∈ actualInverseException Y small a delta V0 S R Z cp P Q U,tripleWeight t) =
      weightedWitness P Q U (actualWitness Y small a delta V0 P S R Z cp) := rfl

theorem normalized_exception_bound (P Q U : Finset ℕ) (witness : (ℕ × ℕ) → ℕ → Prop)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (h : weightedWitness P Q U witness ≤ sigma*(harmonicMass P*harmonicMass Q*harmonicMass U)) :
    weightedWitness P Q U witness/(harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma := by
  have hm : 0 ≤ harmonicMass P*harmonicMass Q*harmonicMass U :=
    mul_nonneg (mul_nonneg (harmonicMass_nonneg P) (harmonicMass_nonneg Q)) (harmonicMass_nonneg U)
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm,div_zero]
    exact hsigma
  · exact (div_le_iff₀ hm).mpr h

theorem structured_outside_actual_exception (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P Q U : Finset ℕ) (p q u : ℕ)
    (hp : p ∈ P) (hq : q ∈ Q) (hu : u ∈ U)
    (hout : ((p,q),u) ∉ actualInverseException Y small a delta V0 S R Z cp P Q U)
    (hbad : WitnessingBadEdge Y small a delta V0 p q u) :
    ∃ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
      aligns (fun p => (a p : ℤ)) t p ∧
        ((t.den*badPrimeProduct (fun p => (a p : ℤ)) t q : ℕ) : ℝ) ≤ R*Z^10 := by
  by_contra hn
  exact hout ((mem_actualInverseException Y small a delta V0 S R Z cp P Q U p q u).mpr
    ⟨hp,hq,hu,hn,hbad⟩)

end ErdosInverseBoxApplication

end

section

namespace ErdosInverseBoxApplication
open ErdosInverseCells ErdosInverseSampleCost ErdosInverseSampling ErdosInverseCounts
  ErdosInverseStructured ErdosInverseAlignment ErdosPrimitiveIntercept
attribute [local instance] Classical.propDecidable

def SourceInverseConclusion (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp sigma : ℝ) (F : ℕ) (P Q U : Finset ℕ) : Prop :=
  (sourceRationalList P (fun p => (a p : ℤ)) S R Z cp).card ≤ F ∧
  (∀ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
    (t.num.natAbs : ℝ) ≤ S*R*Z^10 ∧ (t.den : ℝ) ≤ R*Z^10 ∧
      cp*(P.card : ℝ) ≤ ((P.filter (aligns (fun p => (a p : ℤ)) t)).card : ℝ)) ∧
  (∑ e ∈ actualInverseException Y small a delta V0 S R Z cp P Q U,tripleWeight e)/
    (harmonicMass P*harmonicMass Q*harmonicMass U) ≤ sigma ∧
  (∀ p ∈ P,∀ q ∈ Q,∀ u ∈ U,
    ((p,q),u) ∉ actualInverseException Y small a delta V0 S R Z cp P Q U →
    WitnessingBadEdge Y small a delta V0 p q u →
    ∃ t ∈ sourceRationalList P (fun p => (a p : ℤ)) S R Z cp,
      aligns (fun p => (a p : ℤ)) t p ∧
        ((t.den*badPrimeProduct (fun p => (a p : ℤ)) t q : ℕ) : ℝ) ≤ R*Z^10)

theorem source_inverse_conclusion_of_bounds (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp sigma : ℝ) (F : ℕ) (P Q U : Finset ℕ)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hsigma : 0 ≤ sigma)
    (hlist : (sourceRationalList P (fun p => (a p : ℤ)) S R Z cp).card ≤ F)
    (hweight : weightedWitness P Q U (actualWitness Y small a delta V0 P S R Z cp) ≤
      sigma*(harmonicMass P*harmonicMass Q*harmonicMass U)) :
    SourceInverseConclusion Y small a delta V0 S R Z cp sigma F P Q U := by
  refine ⟨hlist,?_,?_,?_⟩
  · intro t ht
    exact (mem_sourceRationalList P (fun p => (a p : ℤ)) hS hR t).mp ht
  · rw [actual_exception_weight]
    exact normalized_exception_bound P Q U _ sigma hsigma hweight
  · exact fun p hp q hq u hu => structured_outside_actual_exception Y small a delta V0 S R Z cp
      P Q U p q u hp hq hu

end ErdosInverseBoxApplication

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxApplication
open NumberTheoryLean ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement
  ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseSampleCost ErdosInverseSampling
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints

theorem exists_inverse_sample_length (aStar : ℝ) (ha : 0 < aStar) :
    ∃ h : ℕ,12 < aStar*(h : ℝ)/2 := by
  obtain ⟨h,hh⟩ := exists_nat_gt (24/aStar)
  refine ⟨h,?_⟩
  have hm := (div_lt_iff₀ ha).mp hh
  nlinarith

theorem actual_source_inverse (Clen Cparent aStar K alpha delta sigma : ℝ)
    (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hd : 0 < delta) (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) :
    ∃ cp : ℝ,0 < cp ∧ ∃ F : ℕ,∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧
      ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,
        ∀ (m : Fin (binCount (sourceW z) z xi) → ℕ)
          (i j : Fin (binCount (sourceW z) z xi)),
          i ≠ j → m i = 0 → m j = 0 →
          ((∑ k,m k : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
          ∀ a : ℕ → ℕ,
          let R := lower (sourceW z) z xi i
          let U := lower (sourceW z) z xi j
          let P := actualBins z xi i
          let Uset := actualBins z xi j
          let Q := cofactorChoices (actualBins z xi) m
          let S := cofactorScale z xi m
          z^alpha ≤ R → R ≤ z^((1 : ℝ)/100) → U ≤ (sourceW z)^K →
          (∀ q ∈ Q,∀ p ∈ P,
            Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent) →
          (∀ q ∈ Q,∀ p ∈ P,∀ u ∈ Uset,
            3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
          SourceInverseConclusion (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
            (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) S R (sourceZ z) cp sigma F P Q Uset := by
  obtain ⟨h,hh⟩ := exists_inverse_sample_length aStar ha
  let cp := sampleGamma (sigma/16) h/32
  have hcp : 0 < cp := div_pos (sampleGamma_pos (sigma/16) h (by positivity)) (by norm_num)
  obtain ⟨xi0,hxi0,hxi01,hWeight⟩ := actual_box_nonstructured_harmonic Clen Cparent aStar K alpha delta sigma h
    hClen hCparent ha ha1 hK halpha hd hsigma hsigma1 hh
  refine ⟨cp,hcp,⌈2/cp^2⌉₊,xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  have hxi1 := hxib.trans hxi01
  filter_upwards [hWeight xi hxi hxib,actual_box_list_card Clen aStar alpha xi cp hClen ha halpha hxi hxi1 hcp,
    source_span_geometry] with z hweight hlist hspan
  intro m i j hij hmi hmj hm a
  dsimp only
  intro hRlo hRhi hUhi hparent hchild
  have hw := hweight m i j hij hmi hmj hm a hRlo hRhi hUhi hparent hchild
  have hl := hlist m i j hm a hRlo hRhi hchild
  apply source_inverse_conclusion_of_bounds
  · exact (actual_cofactorScale_pos hspan.1 hspan.2.1 hxi m).le
  · exact (endpoint_pos hspan.1 i.1).le
  · exact hsigma.le
  · exact hl
  · exact hw

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
