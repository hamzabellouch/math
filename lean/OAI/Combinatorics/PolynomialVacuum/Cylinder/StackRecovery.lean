import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackProperties

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

noncomputable def spinOfCharge (z : ℤ) : Spin :=
  if z=1 then .plus else if z= -1 then .minus else .zero

theorem charge_spinOfCharge (z : ℤ) (hz : z=0 ∨ z=1 ∨ z= -1) : charge (spinOfCharge z)=z := by
  rcases hz with rfl | rfl | rfl <;> norm_num [spinOfCharge,charge]

omit [NeZero M] in
theorem localIce_values (q : Edge M →₀ ℤ) (v : Vertex M) (h : LocalIce q v) (s : Fin 3) :
    orientedFlow q (v,s)=0 ∨ orientedFlow q (v,s)=1 ∨ orientedFlow q (v,s)= -1 := by
  rcases h with h | ⟨i,o,hio,h⟩
  · exact Or.inl (h s)
  · rw [h s]
    split_ifs <;> norm_num

omit [NeZero M] in
theorem supported_ice_values (D : Finset (Vertex M)) (q : Edge M →₀ ℤ)
    (hi : ∀v∈D,LocalIce q v) (hs : SupportedAt D q) (e : Edge M) :
    q e=0 ∨ q e=1 ∨ q e= -1 := by
  rcases e with ⟨⟨i,j⟩,s⟩
  by_cases hu : (Vertex.up i j : Vertex M)∈D
  · simpa only [orientedFlow_up] using localIce_values q _ (hi _ hu) s
  · by_cases hd : neighbor (.up i j) s∈D
    · have hh := localIce_values q _ (hi _ hd) s
      change orientedFlow q (reverseGerm (.up i j,s))=0 ∨
        orientedFlow q (reverseGerm (.up i j,s))=1 ∨
        orientedFlow q (reverseGerm (.up i j,s))= -1 at hh
      rw [orientedFlow_reverse,orientedFlow_up] at hh
      omega
    · exact Or.inl (by simpa only [orientedFlow_up] using hs (.up i j,s) hu hd)

noncomputable def recoverVertical (H : ℕ) (q : Edge M →₀ ℤ) : Fin (H+1) → ZMod M → Spin :=
  fun j i => spinOfCharge (-q ((i,j.val),0))
noncomputable def recoverAuxiliary (H : ℕ) (q : Edge M →₀ ℤ) : Fin H → ZMod M → Spin :=
  fun j i => spinOfCharge (q ((i,j.val),2))
noncomputable def recoverInternal (H : ℕ) (q : Edge M →₀ ℤ) : Fin H → ZMod M → Spin :=
  fun j i => spinOfCharge (-q ((i,j.val),1))

private theorem outside_vertical_zero (H : ℕ) (q : Edge M →₀ ℤ)
    (hs : SupportedAt (bandSites M H) q) (i : ZMod M) (j : ℤ)
    (hj : ¬(0≤j ∧ j<((H+1 : ℕ) : ℤ))) : q ((i,j),0)=0 := by
  rw [← orientedFlow_up q i j 0]
  apply hs (.up i j,0)
  · simp only [mem_bandSites,InBand,vertexLayer]
    omega
  · simp only [reverseGerm,neighbor,ite_true,mem_bandSites,InBand,vertexLayer]
    omega

private theorem outside_horizontal_zero (H : ℕ) (q : Edge M →₀ ℤ)
    (hs : SupportedAt (bandSites M H) q) (i : ZMod M) (j : ℤ) (s : Fin 3)
    (h0 : s≠0) (hj : ¬(0≤j ∧ j<(H : ℤ))) : q ((i,j),s)=0 := by
  rw [← orientedFlow_up q i j s]
  apply hs (.up i j,s)
  · simpa only [mem_bandSites,InBand,vertexLayer] using hj
  · fin_cases s <;> simp_all [reverseGerm,neighbor,mem_bandSites,InBand,vertexLayer]

 

theorem recover_stack (q : Edge M →₀ ℤ)
    (hi : ∀v∈bandSites M H,LocalIce q v) (hs : SupportedAt (bandSites M H) q) :
    stackCurrent (recoverVertical H q) (recoverAuxiliary H q) (recoverInternal H q)=q := by
  have hv (e : Edge M) : q e=0 ∨ q e=1 ∨ q e= -1 := supported_ice_values _ q hi hs e
  have hn (e : Edge M) : -q e=0 ∨ -q e=1 ∨ -q e= -1 := by have hh:=hv e; omega
  ext ⟨⟨i,j⟩,s⟩
  rw [stackCurrent_apply]
  unfold stackValues
  fin_cases s
  · change -charge (extendSpins (recoverVertical H q) j i)=q ((i,j),0)
    by_cases hj : 0≤j ∧ j<((H+1 : ℕ) : ℤ)
    · simp only [extendSpins,dite_eq_left hj,recoverVertical]
      have he : (j.toNat : ℤ)=j := Int.toNat_of_nonneg hj.1
      rw [he,charge_spinOfCharge _ (hn _),neg_neg]
    · simp only [extendSpins,dite_eq_right hj,charge,neg_zero]
      exact (outside_vertical_zero H q hs i j hj).symm
  · change -charge (extendSpins (recoverInternal H q) j i)=q ((i,j),1)
    by_cases hj : 0≤j ∧ j<(H : ℤ)
    · simp only [extendSpins,dite_eq_left hj,recoverInternal]
      have he : (j.toNat : ℤ)=j := Int.toNat_of_nonneg hj.1
      rw [he,charge_spinOfCharge _ (hn _),neg_neg]
    · simp only [extendSpins,dite_eq_right hj,charge,neg_zero]
      exact (outside_horizontal_zero H q hs i j 1 (by decide) hj).symm
  · change charge (extendSpins (recoverAuxiliary H q) j i)=q ((i,j),2)
    by_cases hj : 0≤j ∧ j<(H : ℤ)
    · simp only [extendSpins,dite_eq_left hj,recoverAuxiliary]
      have he : (j.toNat : ℤ)=j := Int.toNat_of_nonneg hj.1
      rw [he,charge_spinOfCharge _ (hv _)]
    · simp only [extendSpins,dite_eq_right hj,charge]
      exact (outside_horizontal_zero H q hs i j 2 (by decide) hj).symm

end PolynomialVacuumCylinder

end OAI
