import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Absorption.ConnectedUnitaryLift
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerMaps

namespace OAI

noncomputable section
namespace NonunitalRelative

section
open NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter
open scoped CStarAlgebra ENNReal

variable {A E D : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E] [CStarAlgebra D]
variable (U : Ultrafilter ℕ) (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)
variable (hc : ∀ a d,Commute (j a) (κ d))
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U
local notation "C" => Centralizer U j

lemma coefficient_transfer (u : unitary C) (x : normCentralizer (A := A) U)
    (a : A) (d : D) :
    ‖((u:C):NE)*NonunitalNormMaps.quotientMap U j (normInclusion U a*(x:NA))*star ((u:C):NE)-
      normInclusion U (j a*κ d)‖ ≤
    ‖RelativeCentral.quotientMap (inclusion U j) ((u:C)*centralMap U j x*star (u:C))-
      diagonal U j κ hc d‖*‖j a‖ := by
  have h := RelativeCentral.norm_right_mul_sub_le_quotient (inclusion U j)
    ((u:C)*centralMap U j x*star (u:C)) (diagonalCentral U j κ hc d) a
  have hcomm : ((u:C):NE)*normInclusion U (j a)=normInclusion U (j a)*((u:C):NE) :=
    (u:C).property a
  have he : ((u:C):NE)*NonunitalNormMaps.quotientMap U j (normInclusion U a*(x:NA))*star ((u:C):NE)-
      normInclusion U (j a*κ d)=
    normInclusion U (j a)*(((u:C):NE)*NonunitalNormMaps.quotientMap U j (x:NA)*star ((u:C):NE)-
      normInclusion U (κ d)) := by
    rw [map_mul,NonunitalNormMaps.quotientMap_inclusion,map_mul,mul_sub]
    rw [←mul_assoc ((u:C):NE) (normInclusion U (j a)),hcomm]
    simp only [mul_assoc]
  rw [he]
  change ‖normInclusion U (j a)*(((u:C):NE)*NonunitalNormMaps.quotientMap U j (x:NA)*star ((u:C):NE)-
      normInclusion U (κ d))‖≤_ at h
  have hn : ‖inclusion U j a‖=‖j a‖ := normInclusion_norm U (j a)
  rwa [hn] at h

lemma unitary_conjugate_inclusion (u : unitary C) (a : A) :
    ((u:C):NE)*normInclusion U (j a)*star ((u:C):NE)=normInclusion U (j a) := by
  have hcomm : ((u:C):NE)*normInclusion U (j a)=normInclusion U (j a)*((u:C):NE) :=
    (u:C).property a
  rw [hcomm,mul_assoc]
  have hu : ((u:C):NE)*star ((u:C):NE)=1 :=
    congrArg (fun z : C => (z:NE)) (Unitary.coe_mul_star_self u)
  rw [hu,mul_one]

end

section
open Pureness NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter CStarAbsorption
open scoped CStarAlgebra ENNReal TensorProduct

variable {A E D : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E] [CStarAlgebra D]
variable (U : Ultrafilter ℕ) (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E) (hc : ∀ a d,Commute (j a) (κ d))
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U
local notation "C" => Centralizer U j

def coefficientSum (l : List (A×D)) : E := (l.map fun z => j z.1*κ z.2).sum

def originalSum (x : D → normCentralizer (A := A) U) (l : List (A×D)) : NA :=
  (l.map fun z => normInclusion U z.1*(x z.2:NA)).sum

def coefficientBound (l : List (A×D)) : ℝ := (l.map fun z => ‖j z.1‖).sum

omit [CStarAlgebra D] in
lemma coefficientBound_nonneg (l : List (A×D)) : 0≤coefficientBound j l := by
  exact List.sum_nonneg (by intro z hz; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz; exact norm_nonneg _)

lemma finite_coefficient_control (u : unitary C) (x : D → normCentralizer (A := A) U)
    (l : List (A×D)) {δ : ℝ} (hδ : 0≤δ)
    (h : ∀ z∈l,‖RelativeCentral.quotientMap (inclusion U j)
      ((u:C)*centralMap U j (x z.2)*star (u:C))-diagonal U j κ hc z.2‖≤δ) :
    ‖((u:C):NE)*NonunitalNormMaps.quotientMap U j (originalSum U x l)*star ((u:C):NE)-
      normInclusion U (coefficientSum j κ l)‖≤coefficientBound j l*δ := by
  induction l with
  | nil => simp [originalSum,coefficientSum,coefficientBound]
  | cons z l ih =>
    have hz := (coefficient_transfer U j κ hc u (x z.2) z.1 z.2).trans
      (mul_le_mul (h z (by simp)) le_rfl (norm_nonneg _) hδ)
    have hl := ih (fun a ha => h a (by simp [ha]))
    simp only [originalSum,coefficientSum,coefficientBound,List.map_cons,List.sum_cons] at hl ⊢
    simp only [map_add,mul_add,add_mul]
    calc
      _=‖(((u:C):NE)*NonunitalNormMaps.quotientMap U j (normInclusion U z.1*(x z.2:NA))*
          star ((u:C):NE)-normInclusion U (j z.1*κ z.2))+
        (((u:C):NE)*NonunitalNormMaps.quotientMap U j ((l.map fun w => normInclusion U w.1*(x w.2:NA)).sum)*
          star ((u:C):NE)-normInclusion U ((l.map fun w => j w.1*κ w.2).sum))‖ := by
        congr 1; noncomm_ring
      _≤δ*‖j z.1‖+(l.map fun w => ‖j w.1‖).sum*δ := (norm_add_le _ _).trans (add_le_add hz hl)
      _=‖j z.1‖*δ+(l.map fun w => ‖j w.1‖).sum*δ := by ring

end

open Pureness NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter CStarAbsorption
open scoped CStarAlgebra ENNReal TensorProduct

universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
variable {A E T : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E] [CStarAlgebra T]
variable [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E) (hc : ∀ a d,Commute (j a) (κ d))
variable (hj : ∃ a : A,j a≠0) (φ : D →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U)
variable (hD : IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
variable (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
variable (hh : ConnectedApproximateInnerHalfFlip f)
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U
local notation "C" => Centralizer U j

include hc hj φ hD hs hf hd hh in
theorem finite_coefficient_approximation {ι : Type*} [Fintype ι]
    (l : ι → List (A×D)) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary C,∀ i,∃ x : NA,
      ‖((u:C):NE)*NonunitalNormMaps.quotientMap U j x*star ((u:C):NE)-
        normInclusion U (coefficientSum j κ (l i))‖<ε := by
  classical
  let G : Finset D := Finset.univ.biUnion (fun i => ((l i).map Prod.snd).toFinset)
  let M : ℝ := ∑ i,coefficientBound j (l i)
  have hM : 0≤M := Finset.sum_nonneg (fun i _ => coefficientBound_nonneg j (l i))
  let δ := ε/(M+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  have hδM : M*δ<ε := by
    have he : (M+1)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
  obtain ⟨u,hu⟩ := relative_half_flip_lift U j κ hc hj φ hD hs f hf hd hh G hδ
  have hx (d : D) : ∃ x : normCentralizer (A := A) U,centralSequenceQuotient U x=φ d :=
    NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U) (φ d)
  choose x hx using hx
  refine ⟨u,fun i => ⟨originalSum U x (l i),?_⟩⟩
  have hb := finite_coefficient_control U j κ hc u x (l i) hδ.le (fun z hz =>
    (hu z.2 (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩)⟩) (x z.2) (hx z.2)).le)
  have hi : coefficientBound j (l i)≤M :=
    Finset.single_le_sum (fun k _ => coefficientBound_nonneg j (l k)) (Finset.mem_univ i)
  exact hb.trans_lt ((mul_le_mul_of_nonneg_right hi hδ.le).trans_lt hδM)

end NonunitalRelative
end

end OAI
