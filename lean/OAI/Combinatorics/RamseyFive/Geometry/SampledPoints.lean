import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.SumPoissonPow
import OAI.Combinatorics.RamseyFive.Geometry.PencilCount

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def sampledPoints (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  S.filter fun x => ¬Unsampled x S ω

lemma not_mem_sampledPoints (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) (x : ℙ K V) :
    x∉sampledPoints S ω ↔ Unsampled x S ω := by
  simp only [sampledPoints,Finset.mem_filter,not_and,not_not]
  refine ⟨fun h r y hy => ?_,fun h _ => h⟩
  apply h (hy ▸ y.property) r y hy

lemma sampledPoints_card {R : ℕ} (S : Finset (ℙ K V)) (ω : Fin R→S→ℕ) :
    (sampledPoints S ω).card≤ sampleCount ω := by
  let F : Finset S := Finset.univ.filter fun y => ¬Unsampled y.val S ω
  have he : F.map (Function.Embedding.subtype _) = sampledPoints S ω := by
    ext x
    simp only [Finset.mem_map,Function.Embedding.subtype_apply,F,Finset.mem_filter,
      Finset.mem_univ,true_and,sampledPoints,Subtype.exists]
    constructor
    · rintro ⟨y,hy,hu,rfl⟩
      exact ⟨hy,hu⟩
    · rintro ⟨hx,hu⟩
      exact ⟨x,hx,hu,rfl⟩
  rw [←he,Finset.card_map]
  calc
    F.card = ∑_y∈F,1 := by simp
    _ ≤ ∑y∈F,∑r,ω r y := Finset.sum_le_sum fun y hy => by
      have hn := (Finset.mem_filter.mp hy).2
      have hp : ∃r,ω r y≠0 := by
        by_contra h
        push Not at h
        apply hn
        intro r z hz
        have he : z=y := Subtype.val_injective hz.symm
        subst z
        exact h r
      obtain ⟨r,hr⟩ := hp
      exact (Nat.one_le_iff_ne_zero.mpr hr).trans (Finset.single_le_sum (f:=fun r => ω r y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
    _ ≤ ∑y:S,∑r,ω r y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = sampleCount ω := Finset.sum_comm

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def decoded (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ} (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  accepted U (sampledPoints S ω) (fun x => pointScore S (O x) (pencil x) (b x) ω)
    ((z:ℝ)/(2*(Nat.card K:ℝ)))

noncomputable def typicalFailures (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) (t : ℝ) {R : ℕ}
    (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  U.filter fun x => Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\E) (b x) ω|

theorem decoded_bounds {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (U S : Finset (ℙ K V)) (hSU : S⊆U) (hS : S.Nonempty)
    (O : ℙ K V→Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (b : ℙ K V→ℝ) {R : ℕ} (ω : Fin R→S→ℕ) (bad : Finset (ℙ K V))
    (hZ : (emptyTests E (hyperplaneSupport S) ω).Nonempty)
    (hm : ∑ H∈emptyTests E (hyperplaneSupport S) ω,
      cellMass S ((Nat.card K:ℝ)/S.card) H≤ ((emptyTests E (hyperplaneSupport S) ω).card:ℝ)/1000)
    (hb : ∀x∈U\bad,b x∈Set.Icc 0 1)
    (hc : ∀x∈U\bad,(9/10:ℝ)≤(1-b x)^R)
    (herr : ∀x∈U\bad,b x*(pencil x∩E).card≤
      ((emptyTests E (hyperplaneSupport S) ω).card:ℝ)/(100*(Nat.card K:ℝ))) :
    let Z := emptyTests E (hyperplaneSupport S) ω
    let W := decoded U S O b Z.card ω
    let t := (Z.card:ℝ)/(10*(Nat.card K:ℝ))
    (99/100:ℝ)*S.card-bad.card-(typicalFailures S S O E b t ω).card≤((W∩S).card:ℝ) ∧
    (W.card:ℝ)≤ sampleCount ω+bad.card+(typicalFailures U S O E b t ω).card+
      100*(Nat.card K:ℝ)^(d+1)/Z.card := by
  dsimp only
  let Z := emptyTests E (hyperplaneSupport S) ω
  let z : ℝ := Z.card
  let q : ℝ := Nat.card K
  let t : ℝ := z/(10*q)
  let W := decoded U S O b Z.card ω
  let TS := typicalFailures S S O E b t ω
  let TU := typicalFailures U S O E b t ω
  let BS := S.filter fun x => t < pencilCount Z x
  let BU := Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*z/q
  have hz : 0<z := Nat.cast_pos.mpr hZ.card_pos
  have hq0 : 0<q := by dsimp [q];linarith
  have hzq : 0<z/q := div_pos hz hq0
  have hBS : (BS.card:ℝ)≤(S.card:ℝ)/100 := empty_training_card S hS Z hZ hm
  have hBU : (BU.card:ℝ)≤100*q^(d+1)/z := empty_ambient_card hdim hd hq Z hZ
  have ht (x : ℙ K V) (hx : x∈U\bad) :
      |pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω)|≤z/q/100 := by
    have hh := (pointScore_exceptional S (O x) E x (hb x hx) ω).trans (herr x hx)
    convert! hh using 1; dsimp [z,q,Z]; ring
  have htrain : S⊆(W∩S)∪(bad∪TS∪BS) := by
    intro x hx
    by_cases hbad : x∈bad∪TS∪BS
    · exact Finset.mem_union_right _ hbad
    apply Finset.mem_union_left
    have hb0 : x∉bad := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hTS : x∉TS := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hBS0 : x∉BS := fun h => hbad (Finset.mem_union_right _ h)
    have hxU : x∈U\bad := Finset.mem_sdiff.mpr ⟨hSU hx,hb0⟩
    refine Finset.mem_inter.mpr ⟨?_,hx⟩
    apply Finset.mem_filter.mpr
    refine ⟨hSU hx,?_⟩
    by_cases hsamp : x∈sampledPoints S ω
    · exact Or.inl hsamp
    apply Or.inr
    have hu := (not_mem_sampledPoints S ω x).mp hsamp
    have htyp : |pointScore S (O x) (pencil x\E) (b x) ω|≤z/q/10 := by
      have hn : ¬t < |pointScore S (O x) (pencil x\E) (b x) ω| :=
        fun h => hTS (Finset.mem_filter.mpr ⟨hx,hu,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hzx : pencilCount Z x≤z/q/10 := by
      have hn : ¬t < pencilCount Z x := fun h => hBS0 (Finset.mem_filter.mpr ⟨hx,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hcoef : 0≤(1-b x)^R ∧ (1-b x)^R≤1 := by
      exact ⟨pow_nonneg (sub_nonneg.mpr (hb x hxU).2) _,
        pow_le_one₀ (sub_nonneg.mpr (hb x hxU).2) (by linarith [(hb x hxU).1])⟩
    have hh := training_separation (z/q) ((1-b x)^R) (pencilCount Z x)
      (pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω))
      (pointScore S (O x) (pencil x\E) (b x) ω) hzq hcoef
      ⟨pencilCount_nonneg Z x,hzx⟩ (ht x hxU) htyp
    change pointScore S (O x) (pencil x) (b x) ω<z/(2*q)
    have he : z/(2*q)=z/q/2 := by ring
    linarith only [hh,he]
  have hamb : W⊆sampledPoints S ω∪(bad∪TU∪BU) := by
    intro x hx
    obtain ⟨hx,hsamp|hA⟩ := Finset.mem_filter.mp hx
    · exact Finset.mem_union_left _ hsamp
    by_contra hn
    have hsamp : x∉sampledPoints S ω := fun h => hn (Finset.mem_union_left _ h)
    have hbad : x∉bad∪TU∪BU := fun h => hn (Finset.mem_union_right _ h)
    have hb0 : x∉bad := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hTU : x∉TU := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hBU0 : x∉BU := fun h => hbad (Finset.mem_union_right _ h)
    have hxU : x∈U\bad := Finset.mem_sdiff.mpr ⟨hx,hb0⟩
    have hu := (not_mem_sampledPoints S ω x).mp hsamp
    have htyp : |pointScore S (O x) (pencil x\E) (b x) ω|≤z/q/10 := by
      have hn : ¬t < |pointScore S (O x) (pencil x\E) (b x) ω| :=
        fun h => hTU (Finset.mem_filter.mpr ⟨hx,hu,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hzx : (4/5:ℝ)*(z/q)≤pencilCount Z x := by
      have hn : ¬pencilCount Z x<(4/5:ℝ)*z/q :=
        fun h => hBU0 (Finset.mem_filter.mpr ⟨Finset.mem_univ x,h⟩)
      convert! le_of_not_gt hn using 1; ring
    have hh := ambient_separation (z/q) ((1-b x)^R) (pencilCount Z x)
      (pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω))
      (pointScore S (O x) (pencil x\E) (b x) ω) hzq (hc x hxU) hzx (ht x hxU) htyp
    change pointScore S (O x) (pencil x) (b x) ω<z/(2*q) at hA
    have he : z/(2*q)=z/q/2 := by ring
    linarith only [hh,hA,he]
  constructor
  · have h1 : S.card≤(W∩S).card+(bad.card+TS.card+BS.card) := by
      exact (Finset.card_le_card htrain).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1r : (S.card:ℝ)≤((W∩S).card:ℝ)+(bad.card+TS.card+BS.card) := by exact_mod_cast h1
    change (99/100:ℝ)*S.card-bad.card-TS.card≤((W∩S).card:ℝ)
    linarith only [h1r,hBS]
  · have h1 : W.card≤(sampledPoints S ω).card+(bad.card+TU.card+BU.card) := by
      exact (Finset.card_le_card hamb).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1r : (W.card:ℝ)≤((sampleCount ω:ℕ):ℝ)+(bad.card+TU.card+BU.card) := by
      exact_mod_cast h1.trans (Nat.add_le_add_right (sampledPoints_card S ω) _)
    change (W.card:ℝ)≤ sampleCount ω+bad.card+TU.card+100*q^(d+1)/z
    linarith only [h1r,hBU]

end SharpRamseyFive.ScoreGeometry

end OAI
