import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.OwnQuery
import OAI.Combinatorics.RamseyFive.Probability.EmptyTestsManySmall

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def pencilCount (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) : ℝ :=
  (Z.filter fun H => Incident x H).card

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma pencilCount_nonneg (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) :
    0≤pencilCount Z x := Nat.cast_nonneg _

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma pencilCount_weight (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) :
    weightOnPencil (fun H => if H∈Z then (1:ℝ) else 0) x=pencilCount Z x := by
  simp [weightOnPencil,incidenceEntry,pencilCount,mul_ite,Finset.sum_ite_mem]

omit [Field K] [Finite K] in
lemma mean_ratio_lower {d : ℕ} (hd : 1≤d) (hq : (10:ℝ)≤Nat.card K) :
    9/(10*(Nat.card K:ℝ))≤(Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d := by
  have hp : (1:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast Q_pos (Nat.card K) (d-1)
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  have he : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 :=
    by exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  apply (div_le_div_iff₀ (by positivity) hQ).mpr
  nlinarith

theorem empty_ambient_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (Z : Finset (ℙ K (Dual K V))) (hZ : Z.Nonempty) :
    ((Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*Z.card/(Nat.card K:ℝ)).card:ℝ)≤
      100*(Nat.card K:ℝ)^(d+1)/Z.card := by
  let z : ℝ := Z.card
  let q : ℝ := Nat.card K
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*z
  let E := Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*z/q
  have hz : 0<z := Nat.cast_pos.mpr hZ.card_pos
  have hq0 : 0<q := by dsimp [q];linarith
  have hμ : 9*z/(10*q)≤μ := by
    have hh := mul_le_mul_of_nonneg_right (mean_ratio_lower hd hq) hz.le
    dsimp [μ,z,q]
    convert! hh using 1; ring
  have hv := pencil_variance hdim hd (fun H => if H∈Z then (1:ℝ) else 0)
  have hsum : (∑ H : ℙ K (Dual K V),(if H∈Z then (1:ℝ) else 0)^2)=z := by
    simp [z,ite_pow]
  simp only [pencilCount_weight,Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter] at hv
  rw [hsum] at hv
  have hvar : ∑x,(pencilCount Z x-μ)^2≤q^(d-1)*z := hv
  have hs : (E.card:ℝ)*(z/(10*q))^2≤∑x,(pencilCount Z x-μ)^2 := by
    calc
      _ = ∑_x∈E,(z/(10*q))^2 := by simp
      _ ≤ ∑x∈E,(pencilCount Z x-μ)^2 := Finset.sum_le_sum fun x hx => by
        have he := (Finset.mem_filter.mp hx).2
        have hh : z/(10*q)≤μ-pencilCount Z x := by
          have hid : 9*z/(10*q)-(4/5:ℝ)*z/q=z/(10*q) := by ring
          linarith only [he,hμ,hid]
        nlinarith [sq_nonneg (μ-pencilCount Z x-z/(10*q)),div_nonneg hz.le (by positivity : 0≤10*q)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun _ _ _ => sq_nonneg _)
  change (E.card:ℝ)≤100*q^(d+1)/z
  calc
    _ ≤ (q^(d-1)*z)/(z/(10*q))^2 := (le_div_iff₀ (sq_pos_of_pos (by positivity))).mpr (hs.trans hvar)
    _ = _ := by
      have he : q^(d+1)=q^(d-1)*q^2 := by rw [←pow_add];congr 1;omega
      rw [he]
      field_simp
      ring

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma pencilCount_training_sum (S : Finset (ℙ K V)) (Z : Finset (ℙ K (Dual K V))) :
    (∑x∈S,pencilCount Z x)=∑H∈Z,((S.filter fun x => Incident x H).card:ℝ) := by
  simp only [pencilCount,←Finset.sum_boole]
  rw [Finset.sum_comm]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma empty_training_mass (S : Finset (ℙ K V)) (hS : S.Nonempty)
    (Z : Finset (ℙ K (Dual K V))) :
    (∑x∈S,pencilCount Z x)=((S.card:ℝ)/(Nat.card K:ℝ))*
      ∑H∈Z,cellMass S ((Nat.card K:ℝ)/S.card) H := by
  rw [pencilCount_training_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  unfold cellMass
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  have hq : (Nat.card K:ℝ)≠0 := (Nat.cast_pos.mpr (Nat.card_pos (α:=K))).ne'
  field_simp

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem empty_training_card (S : Finset (ℙ K V)) (hS : S.Nonempty)
    (Z : Finset (ℙ K (Dual K V))) (hZ : Z.Nonempty)
    (hm : ∑H∈Z,cellMass S ((Nat.card K:ℝ)/S.card) H≤(Z.card:ℝ)/1000) :
    ((S.filter fun x => (Z.card:ℝ)/(10*(Nat.card K:ℝ))<pencilCount Z x).card:ℝ)≤
      (S.card:ℝ)/100 := by
  let E := S.filter fun x => (Z.card:ℝ)/(10*(Nat.card K:ℝ))<pencilCount Z x
  have hq : (0:ℝ)<Nat.card K := Nat.cast_pos.mpr (Nat.card_pos (α:=K))
  have hz : (0:ℝ)<Z.card := Nat.cast_pos.mpr hZ.card_pos
  have hs : (E.card:ℝ)*((Z.card:ℝ)/(10*(Nat.card K:ℝ)))≤
      ((S.card:ℝ)/(Nat.card K:ℝ))*((Z.card:ℝ)/1000) := by
    calc
      _ = ∑_x∈E,(Z.card:ℝ)/(10*(Nat.card K:ℝ)) := by simp
      _ ≤ ∑x∈E,pencilCount Z x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
      _ ≤ ∑x∈S,pencilCount Z x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset ..) (fun x _ _ => pencilCount_nonneg Z x)
      _ = _ := empty_training_mass S hS Z
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  apply (mul_le_mul_iff_left₀ (by positivity : 0<(Z.card:ℝ)/(10*(Nat.card K:ℝ)))).mp
  convert! hs using 1; ring

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def hyperplaneSupport (S : Finset (ℙ K V)) (H : ℙ K (Dual K V)) : Finset S :=
  Finset.univ.filter fun y => Incident y.val H

noncomputable def ownSupport (S O : Finset (ℙ K V)) : Finset S :=
  Finset.univ.filter fun y => y.val∈O

omit [Finite K] [FiniteDimensional K V] in
lemma pointScore_eq_sum (S O : Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) :
    pointScore S O F b ω=∑ H∈F,ownScore (hyperplaneSupport S H) (ownSupport S O) b ω := by
  unfold pointScore
  rw [←Finset.sum_coe_sort F]
  apply Finset.sum_congr rfl
  intro H _
  unfold ownScore
  apply Finset.prod_congr rfl
  intro r _
  have ho : ω r∈emptyEvent (hyperplaneSupport S H.val∩ownSupport S O) ↔
      ∀y:S,y.val∈O → Incident y.val H.val → ω r y=0 := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      Finset.mem_inter,hyperplaneSupport,ownSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h y hy hI => h y ⟨hI,hy⟩,fun h y hy => h y hy.2 hy.1⟩
  have he : ω r∈emptyEvent (hyperplaneSupport S H.val\ownSupport S O) ↔
      ∀y:S,y.val∉O → Incident y.val H.val → ω r y=0 := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      Finset.mem_sdiff,hyperplaneSupport,ownSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h y hy hI => h y ⟨hI,hy⟩,fun h y hy => h y hy.2 hy.1⟩
  simp only [emptyIndicator,Set.indicator_apply,ho,he]

omit [Finite K] [FiniteDimensional K V] in
lemma pointScore_split (S O : Finset (ℙ K V)) (F E : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) :
    pointScore S O F b ω=pointScore S O (F∩E) b ω+pointScore S O (F\E) b ω := by
  simp only [pointScore_eq_sum]
  exact (Finset.sum_inter_add_sum_sdiff F E _).symm

variable [Fintype (ℙ K (Dual K V))]
noncomputable def pencil (x : ℙ K V) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun H => Incident x H

omit [Finite K] [FiniteDimensional K V] in
lemma emptyTests_pencil (S : Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (x : ℙ K V) {R : ℕ} (ω : Fin R→S→ℕ) :
    emptyTests (pencil x∩E) (hyperplaneSupport S) ω=
      (emptyTests E (hyperplaneSupport S) ω).filter fun H => Incident x H := by
  ext H
  simp only [emptyTests,Finset.mem_filter,Finset.mem_inter,pencil,Finset.mem_univ,true_and]
  tauto

omit [Finite K] [FiniteDimensional K V] in
theorem pointScore_exceptional (S O : Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (x : ℙ K V) {R : ℕ} {b : ℝ} (hb : b∈Set.Icc 0 1) (ω : Fin R→S→ℕ) :
    |pointScore S O (pencil x) b ω-
      ((1-b)^R*pencilCount (emptyTests E (hyperplaneSupport S) ω) x+
        pointScore S O (pencil x\E) b ω)|≤b*(pencil x∩E).card := by
  rw [pointScore_split S O (pencil x) E]
  have hh := exceptionalScore_error (pencil x∩E) (hyperplaneSupport S) (ownSupport S O) hb ω
  rw [←pointScore_eq_sum,emptyTests_pencil] at hh
  simpa only [pencilCount,add_sub_add_right_eq_sub] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
