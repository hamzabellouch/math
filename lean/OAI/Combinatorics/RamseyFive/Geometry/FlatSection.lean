import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FlatPoints
import OAI.Combinatorics.RamseyFive.Entropy.Map
import OAI.Combinatorics.RamseyFive.Geometry.GeometricRestriction

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence ProjectiveTraining
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def flatEmbedding (A : Submodule K V) : ℙ K A ↪ ℙ K V :=
  ⟨Projectivization.map A.subtype A.injective_subtype,
    Projectivization.map_injective A.subtype A.injective_subtype⟩

noncomputable def flatSection (A : Submodule K V) (X : Finset (ℙ K V)) : Finset (ℙ K A) :=
  X.preimage (flatEmbedding A) (flatEmbedding A).injective.injOn

lemma section_mono (A : Submodule K V) {X Y : Finset (ℙ K V)} (hXY : X⊆Y) :
    flatSection A X⊆flatSection A Y := by
  intro x hx
  simpa only [flatSection,Finset.mem_preimage] using hXY (Finset.mem_preimage.mp hx)

lemma range_flatEmbedding (A : Submodule K V) (p : ℙ K V) :
    p∈Set.range (flatEmbedding A) ↔ p.submodule≤A := by
  constructor
  · rintro ⟨x,rfl⟩
    induction x using Projectivization.ind with | h v hv =>
    change (Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K v hv)).submodule≤A
    rw [Projectivization.map_mk,Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact v.property
  · intro hp
    have hm : p.rep∈A := hp (by rw [p.submodule_eq]; exact Submodule.mem_span_singleton_self p.rep)
    have hn : (⟨p.rep,hm⟩:A)≠0 := fun hz=>p.rep_nonzero (congrArg Subtype.val hz)
    refine ⟨Projectivization.mk K (⟨p.rep,hm⟩:A) hn,?_⟩
    change Projectivization.map A.subtype A.injective_subtype (Projectivization.mk K (⟨p.rep,hm⟩:A) hn)=p
    rw [Projectivization.map_mk]
    exact p.mk_rep

variable [Finite K] [FiniteDimensional K V]

lemma section_map (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).map (flatEmbedding A)=X∩flatPoints A := by
  ext x
  simp only [Finset.mem_map,flatSection,Finset.mem_preimage,Finset.mem_inter,mem_flatPoints]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,(range_flatEmbedding A _).mp ⟨a,rfl⟩⟩
  · rintro ⟨hx,hflat⟩
    obtain ⟨a,rfl⟩ := (range_flatEmbedding A x).mpr hflat
    exact ⟨a,hx,rfl⟩

lemma section_card (A : Submodule K V) (X : Finset (ℙ K V)) :
    (flatSection A X).card=(X∩flatPoints A).card := by
  rw [←section_map,Finset.card_map]

lemma section_degree_sum (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)=incidences (X∩flatPoints A) T := by
  rw [←section_map,incidences_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_map]
  simp only [flatDegree, incidenceEntry, Finset.sum_boole]
  rfl

omit [Finite K] [FiniteDimensional K V] in
lemma incidences_mono_left {X Y : Finset (ℙ K V)} (T : Finset (ℙ K (Dual K V))) (hXY : X⊆Y) :
    incidences X T ≤ incidences Y T := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.product_subset_product hXY (Finset.Subset.refl _)

lemma section_density (A : Submodule K V) (X : Finset (ℙ K V))
    (T : Finset (ℙ K (Dual K V))) (τ : ℝ)
    (h : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    ∑p∈T,(flatDegree A (flatSection A X) p:ℝ)≤τ*X.card*T.card/(Nat.card K) := by
  rw [section_degree_sum]
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  apply (le_div_iff₀ hq).mpr
  have hi : (incidences (X∩flatPoints A) T:ℝ) ≤ incidences X T := by
    exact_mod_cast incidences_mono_left T (Finset.inter_subset_left (s₁:=X) (s₂:=flatPoints A))
  nlinarith only [mul_le_mul_of_nonneg_left hi hq.le,h]

omit [Finite K] [FiniteDimensional K V] in
lemma section_decoder (A : Submodule K V) (X U : Finset (ℙ K V)) (Z : Finset (ℙ K A))
    (hZU : Z⊆flatSection A U) :
    Z.map (flatEmbedding A)⊆U ∧ (Z.map (flatEmbedding A)).card=Z.card ∧
    ((Z.map (flatEmbedding A))∩X).card=(Z∩flatSection A X).card := by
  refine ⟨?_,Finset.card_map _,?_⟩
  · rintro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_map.mp hx
    exact Finset.mem_preimage.mp (hZU hy)
  · have he : ((Z.map (flatEmbedding A))∩X)=(Z∩flatSection A X).map (flatEmbedding A) := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_map,flatSection,Finset.mem_preimage]
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,hx⟩
        exact ⟨y,⟨hy,hx⟩,rfl⟩
      · rintro ⟨y,⟨hy,hx⟩,rfl⟩
        exact ⟨⟨y,hy,rfl⟩,hx⟩
    rw [he,Finset.card_map]

end

open Module ProjectiveIncidence ProjectiveTraining DyadicLifts
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

theorem original_large_cell (A : Submodule K V)
    (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hX : X.Nonempty) (hT : T.Nonempty) (hXU : X⊆UX) (hTU : T⊆UT)
    (τ b : ℝ) (hτ : 0<τ) (hsmall : Real.sqrt τ≤1/200)
    (hflat : (X.card:ℝ)≤100*(X∩flatPoints A).card)
    (hprod : (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hdens : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    let S := flatSection A X
    let US := flatSection A UX
    let M := (Nat.card K)^(finrank K V-finrank K A)
    let L := Nat.log 2 M+1
    let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
    S.Nonempty ∧ S⊆US ∧ S.card≤X.card ∧ (X.card:ℝ)≤100*S.card ∧
    ∃k≤Nat.log 2 M,
      let T₀ := restrictions (image A.dualRestrict) G k
      let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
      T₀.Nonempty ∧ T₀⊆UT₀ ∧
      (Nat.card K:ℝ)^(finrank K A)*Real.exp (-(b+Real.log (400*L)))≤(S.card:ℝ)*T₀.card ∧
      (∀p∈T₀,((S.filter fun x=>Incident x p).card:ℝ)≤(Real.sqrt τ/(Nat.card K))*S.card) ∧
      (Nat.card K:ℝ)*(incidences S T₀:ℝ)≤Real.sqrt τ*S.card*T₀.card ∧
      Real.log ((UT₀.card:ℝ)/T₀.card)≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*L) ∧
      Real.log ((US.card:ℝ)/S.card)≤Real.log ((UX.card:ℝ)/X.card)+Real.log 100 := by
  dsimp only
  have hx : (0:ℝ)<X.card := by exact_mod_cast hX.card_pos
  have hxs : (X.card:ℝ)≤100*(flatSection A X).card := by simpa only [section_card] using hflat
  have hs : (0:ℝ)<(flatSection A X).card := by nlinarith only [hx,hxs]
  have hS : (flatSection A X).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hs)
  have hSU := section_mono A hXU
  have hsX : (flatSection A X).card≤X.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  have huX : (flatSection A UX).card≤UX.card := by rw [section_card];exact Finset.card_le_card Finset.inter_subset_left
  obtain ⟨k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ := large_cell_pair_with_losses
    A (flatSection A X) T UT hS hT hTU X.card τ b hx hτ hsmall hxs hprod
    (section_density A X T τ hdens)
  refine ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,?_⟩
  apply hsgap (flatSection A UX).card UX.card
  · exact_mod_cast (hS.mono hSU).card_pos
  · exact_mod_cast huX

end SharpRamseyFive.ProjectiveRestriction

end OAI
