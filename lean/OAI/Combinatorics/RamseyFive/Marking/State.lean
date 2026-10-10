import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.SubspacePointsEquiv

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def state (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (E : Finset ι) (y : ℙ K (Dual K V)) : Submodule K (Dual K V) :=
  ⨆ i∈E, if Incident (a i) y then (b i).submodule else ⊥

lemma state_empty (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V)) (y : ℙ K (Dual K V)) :
    state a b ∅ y=⊥ := by
  apply le_antisymm ?_ bot_le
  apply iSup₂_le
  intro i hi
  exact False.elim (Finset.notMem_empty i hi)

lemma state_insert [DecidableEq ι] (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (E : Finset ι) (i : ι) (y : ℙ K (Dual K V)) :
    state a b (insert i E) y =
      (if Incident (a i) y then (b i).submodule else ⊥) ⊔ state a b E y := by
  simp only [state,Finset.mem_insert,iSup_or,iSup_sup_eq,iSup_iSup_eq_left]

lemma state_mono (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    {E F : Finset ι} (hEF : E⊆F) (y : ℙ K (Dual K V)) :
    state a b E y≤ state a b F y := by
  apply iSup₂_le
  intro i hi
  exact le_iSup_of_le i (le_iSup_of_le (hEF hi) le_rfl)

def Consistent [LT ι] (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V)) : Prop :=
  ∀ i j,i<j → Incident (a i) (b j) → Incident (a j) (b i)

lemma state_le_annihilator [LT ι] (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (hF : Consistent a b) (E : Finset ι) (j : ι) (hE : ∀ i∈E,i<j) :
    state a b E (b j)≤(a j).submodule.dualAnnihilator := by
  apply iSup₂_le
  intro i hi
  split_ifs with hab
  · exact (incident_iff_dualAnnihilator _ _).mp (hF i j (hE i hi) hab)
  · exact bot_le

lemma state_rank_le [FiniteDimensional K V] [LT ι]
    (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (hF : Consistent a b) (E : Finset ι) (j : ι) (hE : ∀ i∈E,i<j) :
    finrank K (state a b E (b j))≤finrank K V-1 := by
  have hr := Submodule.finrank_mono (state_le_annihilator a b hF E j hE)
  have hdim := Subspace.finrank_add_finrank_dualAnnihilator_eq (a j).submodule
  rw [(a j).finrank_submodule] at hdim
  omega

lemma update_strict [FiniteDimensional K V] [DecidableEq ι]
    (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (E : Finset ι) (i : ι) (y : ℙ K (Dual K V))
    (hhit : Incident (a i) y) (hnew : ¬(b i).submodule≤ state a b E y) :
    finrank K (state a b E y)<finrank K (state a b (insert i E) y) := by
  rw [state_insert,ite_eq_left hhit]
  apply Submodule.finrank_lt_finrank_of_lt
  exact lt_of_le_of_ne le_sup_right (fun h => hnew (h ▸ le_sup_left))

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)]

lemma subspace_finset_card (W : Submodule K V) :
    (Finset.univ.filter fun p : ℙ K V => p.submodule≤W).card =
      ∑ i∈Finset.range (finrank K W),Nat.card K^i := by
  rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card]
  exact card_subspacePoints W

noncomputable def memberships (W : Y → Submodule K V) (Z : Finset Y) (b : ℙ K V) : ℕ :=
  (Z.filter fun y => b.submodule≤W y).card

lemma sum_memberships (W : Y → Submodule K V) (Z : Finset Y) (l : ℕ)
    (hW : ∀ y∈Z,finrank K (W y)=l) :
    (∑ b : ℙ K V,(memberships W Z b:ℝ)) =
      (Z.card:ℝ)*(∑ i∈Finset.range l,(Nat.card K:ℝ)^i) := by
  simp only [memberships,←Finset.sum_boole]
  rw [Finset.sum_comm]
  have hh (y : Y) (hy : y∈Z) :
      (∑ b : ℙ K V,if b.submodule≤W y then (1:ℝ) else 0)=
        ∑ i∈Finset.range l,(Nat.card K:ℝ)^i := by
    rw [Finset.sum_boole,subspace_finset_card,hW y hy]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hh,Finset.sum_const,nsmul_eq_mul]

lemma q_mul_geometric_bound (q : ℝ) (hq : 2≤q) (l : ℕ) :
    q*(∑ i∈Finset.range l,q^i)≤2*q^l := by
  have hp := pow_nonneg (by linarith : 0≤q) l
  have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.range l) => pow_nonneg (by linarith : 0≤q) i)
  have he := geom_sum_mul q l
  have hn := mul_nonneg hs (by linarith : 0≤q-2)
  nlinarith

theorem popular_count (W : Y → Submodule K V) (Z : Finset Y) (hZ : Z.Nonempty)
    (l : ℕ) (hW : ∀ y∈Z,finrank K (W y)=l) :
    ((Finset.univ.filter fun b : ℙ K V =>
      (Z.card:ℝ)/(16*Nat.card K)≤ memberships W Z b).card:ℝ) ≤
      32*(Nat.card K:ℝ)^l := by
  let B := Finset.univ.filter fun b : ℙ K V =>
      (Z.card:ℝ)/(16*Nat.card K)≤ memberships W Z b
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hZpos : (0:ℝ)<Z.card := by exact_mod_cast Finset.card_pos.mpr hZ
  have hs : (B.card:ℝ)*((Z.card:ℝ)/(16*Nat.card K))≤∑ b:ℙ K V,(memberships W Z b:ℝ) := by
    calc
      _ = ∑ b∈B,(Z.card:ℝ)/(16*Nat.card K) := by simp
      _ ≤ ∑ b∈B,(memberships W Z b:ℝ) := Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
  rw [sum_memberships W Z l hW] at hs
  have hm := mul_le_mul_of_nonneg_right hs (show (0:ℝ)≤16*Nat.card K by positivity)
  have he : (B.card:ℝ)*((Z.card:ℝ)/(16*Nat.card K))*(16*Nat.card K)=B.card*Z.card := by
    have hq0 : (Nat.card K:ℝ)≠0 := by linarith
    field_simp
  rw [he] at hm
  have hgeom := q_mul_geometric_bound (Nat.card K:ℝ) hq l
  have hc : (B.card:ℝ)*Z.card ≤ (32*(Nat.card K:ℝ)^l)*Z.card := by
    nlinarith [mul_le_mul_of_nonneg_right hgeom (show (0:ℝ)≤16*Z.card by positivity)]
  change (B.card:ℝ) ≤ 32*(Nat.card K:ℝ)^l
  exact (mul_le_mul_iff_left₀ hZpos).mp (by simpa only [mul_comm] using hc)

end SharpRamseyFive.Marking

end OAI
