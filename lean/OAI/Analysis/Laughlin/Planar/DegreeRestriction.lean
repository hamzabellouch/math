import OAI.Analysis.Laughlin.Fock.ModeEmbedding
import OAI.Analysis.Laughlin.Fock.Hamiltonian
import OAI.Analysis.Laughlin.Planar.Model

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_fin_castLE_of_high_zero {R : Type*} [AddCommMonoid R]
    (L Q : ℕ) (h : L ≤ Q) (f : Fin (Q+1) → R)
    (hf : ∀ i, L < i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin (L+1), f (Fin.castLE (Nat.add_le_add_right h 1) i) := by
  classical
  let e := Fin.castLEEmb (Nat.add_le_add_right h 1)
  have hz : ∑ i ∈ Finset.univ.map e, f i = ∑ i : Fin (Q+1), f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    apply hf
    by_contra hh
    have hiL : i.val ≤ L := by omega
    apply hin
    exact Finset.mem_map.mpr ⟨⟨i.val,by omega⟩,Finset.mem_univ _,Fin.ext rfl⟩
  rw [← hz,Finset.sum_map]
  rfl

theorem pairEnd_fockInclusion (L Q : ℕ) (h : L ≤ Q)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ) (x : Space L) :
    pairEnd Q c (fockInclusion L Q h x) =
      fockInclusion L Q h (pairEnd L
        (fun i j => c (Fin.castLE (Nat.add_le_add_right h 1) i)
          (Fin.castLE (Nat.add_le_add_right h 1) j)) x) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul]
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro i hi
    simp [fockInclusion_annihilate_high L Q h i hi])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro j hj
    rw [fockInclusion_annihilate]
    simp [fockInclusion_annihilate_high L Q h j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fockInclusion_annihilate,fockInclusion_annihilate]

theorem pairCreateEnd_fockInclusion (L Q : ℕ) (h : L ≤ Q)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : ∀ i j, L < i.val ∨ L < j.val → c i j = 0) (x : Space L) :
    pairCreateEnd Q c (fockInclusion L Q h x) =
      fockInclusion L Q h (pairCreateEnd L
        (fun i j => c (Fin.castLE (Nat.add_le_add_right h 1) i)
          (Fin.castLE (Nat.add_le_add_right h 1) j)) x) := by
  simp only [pairCreateEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    map_sum,map_smul]
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro i hi
    simp only [hc i _ (Or.inl hi),star_zero,zero_smul,Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro j hj
    simp only [hc _ j (Or.inr hj),star_zero,zero_smul])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← fockInclusion_create,← fockInclusion_create]

def DegreeAtMost (Q d : ℕ) (x : Space Q) : Prop :=
  ∀ A : Finset (Fin (Q+1)), d < ∑ i ∈ A, i.val → (occupationBasis Q).repr x A = 0

theorem two_mem_weight_le (Q : ℕ) (A : Finset (Fin (Q+1))) (i j : Fin (Q+1))
    (hi : i ∈ A) (hj : j ∈ A) (hij : i ≠ j) :
    i.val+j.val ≤ ∑ k ∈ A, k.val := by
  have hs : ({i,j} : Finset (Fin (Q+1))) ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · simpa only [hk] using hi
    · have he := Finset.mem_singleton.mp hk
      simpa only [he] using hj
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun k hk hnot => Nat.zero_le k.val)
  simpa [hij] using hsum

theorem pair_annihilate_high_degree (Q d : ℕ) (x : Space Q) (hx : DegreeAtMost Q d x)
    (i j : Fin (Q+1)) (hij : d < i.val+j.val) :
    annihilate j (annihilate i x) = 0 := by
  by_cases he : i=j
  · subst j
    exact LinearMap.congr_fun (annihilate_sq i) x
  conv_lhs => rw [← (occupationBasis Q).sum_repr x]
  simp only [map_sum,map_smul]
  apply Finset.sum_eq_zero
  intro A hA
  by_cases hd : d < ∑ k ∈ A, k.val
  · rw [hx A hd,zero_smul]
  by_cases hi : i ∈ A
  · rw [annihilate_occupied Q i A hi,map_smul]
    have hj : j ∉ A.erase i := by
      intro hj
      have hjA := (Finset.mem_erase.mp hj).2
      have hh := two_mem_weight_le Q A i j hi hjA he
      omega
    rw [annihilate_unoccupied Q j (A.erase i) hj,smul_zero,smul_zero]
  · rw [annihilate_unoccupied Q i A hi,map_zero,smul_zero]

theorem pairEnd_high_degree (Q d p : ℕ) (x : Space Q) (hx : DegreeAtMost Q d x)
    (hp : d < p+1) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : ∀ i j, i.val+j.val ≠ p+1 → c i j = 0) : pairEnd Q c x = 0 := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases he : i.val+j.val=p+1
  · rw [pair_annihilate_high_degree Q d x hx i j (by omega),smul_zero]
  · rw [hc i j he,zero_smul]

noncomputable def restrictedSpherePairEnd (L Q p : ℕ) : Module.End ℂ (Space L) :=
  pairEnd L (fun i j => Planar.sphereCoefficient Q p i.val j.val)

noncomputable def restrictedSpherePairCreateEnd (L Q p : ℕ) : Module.End ℂ (Space L) :=
  pairCreateEnd L (fun i j => Planar.sphereCoefficient Q p i.val j.val)

noncomputable def restrictedSphereHamiltonian (L Q : ℕ) : Module.End ℂ (Space L) :=
  ∑ p ∈ Finset.range (2*L+1), restrictedSpherePairCreateEnd L Q p * restrictedSpherePairEnd L Q p

noncomputable def restrictedSphereEnergy (L Q : ℕ) (x : Space L) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), occupationNormSq L (restrictedSpherePairEnd L Q p x)

theorem sourcePairEnd_fockInclusion (L Q p : ℕ) (h : L ≤ Q)
    (hQ : 0 < Q) (hp : p ≤ 2*Q-2) (x : Space L) :
    sourcePairEnd Q p (fockInclusion L Q h x) =
      fockInclusion L Q h (restrictedSpherePairEnd L Q p x) := by
  unfold sourcePairEnd
  rw [pairEnd_fockInclusion]
  unfold restrictedSpherePairEnd
  congr 2
  congr 1
  funext i j
  exact (Planar.sphereCoefficient_eq Q p hQ hp
    (Fin.castLE (Nat.add_le_add_right h 1) i) (Fin.castLE (Nat.add_le_add_right h 1) j)).symm

theorem restrictedSpherePairEnd_high_degree (L Q d p : ℕ) (x : Space L)
    (hx : DegreeAtMost L d x) (hp : d < p+1) : restrictedSpherePairEnd L Q p x = 0 := by
  apply pairEnd_high_degree L d p x hx hp
  intro i j hij
  simp [Planar.sphereCoefficient,pairLimitCoefficient,hij]

theorem sourcePairCreateEnd_fockInclusion (L Q p : ℕ) (h : L ≤ Q)
    (hQ : 0 < Q) (hp : p+1 ≤ L) (x : Space L) :
    sourcePairCreateEnd Q p (fockInclusion L Q h x) =
      fockInclusion L Q h (restrictedSpherePairCreateEnd L Q p x) := by
  have hpQ : p ≤ 2*Q-2 := by omega
  unfold sourcePairCreateEnd
  rw [pairCreateEnd_fockInclusion L Q h _ (by
    intro i j hij
    have hne : i.val+j.val ≠ p+1 := by rcases hij with hi | hj <;> omega
    simp [pairCoefficient,hne])]
  unfold restrictedSpherePairCreateEnd
  congr 2
  congr 1
  funext i j
  exact (Planar.sphereCoefficient_eq Q p hQ hpQ
    (Fin.castLE (Nat.add_le_add_right h 1) i) (Fin.castLE (Nat.add_le_add_right h 1) j)).symm

theorem sum_range_eq_short {M : Type*} [AddCommMonoid M] (n m : ℕ) (hnm : n ≤ m)
    (f : ℕ → M) (hf : ∀ k, n ≤ k → k < m → f k = 0) :
    (∑ k ∈ Finset.range m, f k) = ∑ k ∈ Finset.range n, f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hnm)
  intro k hk hkn
  exact hf k (by simpa using hkn) (Finset.mem_range.mp hk)

theorem sourceFockHamiltonian_fockInclusion (L Q : ℕ) (hQ : L+2 ≤ Q)
    (x : Space L) (hx : DegreeAtMost L L x) :
    sourceFockHamiltonian Q (fockInclusion L Q (by omega) x) =
      fockInclusion L Q (by omega) (restrictedSphereHamiltonian L Q x) := by
  have h : L ≤ Q := by omega
  have hsource (p : ℕ) (hp : L ≤ p) (hpQ : p < 2*Q-1) :
      sourcePairEnd Q p (fockInclusion L Q h x) = 0 := by
    rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),
      restrictedSpherePairEnd_high_degree L Q L p x hx (by omega),map_zero]
  simp only [sourceFockHamiltonian,restrictedSphereHamiltonian,LinearMap.sum_apply,
    Module.End.mul_apply,map_sum]
  rw [sum_range_eq_short L (2*Q-1) (by omega) _ (by
    intro p hp hpQ
    rw [hsource p hp hpQ,map_zero])]
  rw [sum_range_eq_short L (2*L+1) (by omega) _ (by
    intro p hp hpL
    rw [restrictedSpherePairEnd_high_degree L Q L p x hx (by omega),map_zero,map_zero])]
  apply Finset.sum_congr rfl
  intro p hp
  have hpL := Finset.mem_range.mp hp
  rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),
    sourcePairCreateEnd_fockInclusion L Q p h (by omega) (by omega)]

theorem sourceFockEnergy_fockInclusion (L Q : ℕ) (hQ : L+2 ≤ Q)
    (x : Space L) (hx : DegreeAtMost L L x) :
    sourceFockEnergy Q (fockInclusion L Q (by omega) x) = restrictedSphereEnergy L Q x := by
  have h : L ≤ Q := by omega
  unfold sourceFockEnergy restrictedSphereEnergy
  rw [sum_range_eq_short L (2*Q-1) (by omega) _ (by
    intro p hp hpQ
    rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),
      restrictedSpherePairEnd_high_degree L Q L p x hx (by omega),map_zero]
    simp [occupationNormSq])]
  rw [sum_range_eq_short L (2*L+1) (by omega) _ (by
    intro p hp hpL
    rw [restrictedSpherePairEnd_high_degree L Q L p x hx (by omega)]
    simp [occupationNormSq])]
  apply Finset.sum_congr rfl
  intro p hp
  have hpL := Finset.mem_range.mp hp
  rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),fockInclusion_normSq]

end Laughlin.Fock

end OAI
