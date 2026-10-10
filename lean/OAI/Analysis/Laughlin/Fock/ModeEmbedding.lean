import OAI.Analysis.Laughlin.Fock.SpinRepresentation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def modeInclusion (L Q : ℕ) (_h : L ≤ Q) : Orbital L →ₗ[ℂ] Orbital Q where
  toFun v j := if hj : j.val ≤ L then v ⟨j.val,by omega⟩ else 0
  map_add' v w := by ext j; dsimp; split_ifs <;> simp
  map_smul' c v := by ext j; dsimp; split_ifs <;> simp

noncomputable def fockInclusion (L Q : ℕ) (h : L ≤ Q) : Space L →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (modeInclusion L Q h)

def includedOccupations (L Q : ℕ) (h : L ≤ Q) (A : Finset (Fin (L+1))) :
    Finset (Fin (Q+1)) := A.map (Fin.castLEEmb (Nat.add_le_add_right h 1))

theorem modeInclusion_mode (L Q : ℕ) (h : L ≤ Q) (i : Fin (L+1)) :
    modeInclusion L Q h (mode i) = mode (Fin.castLE (Nat.add_le_add_right h 1) i) := by
  ext j
  change (if hj : j.val ≤ L then (Pi.single i (1 : ℂ) : Orbital L) ⟨j.val,by omega⟩ else 0) =
    (Pi.single (Fin.castLE (Nat.add_le_add_right h 1) i) (1 : ℂ) : Orbital Q) j
  by_cases hj : j.val ≤ L
  · rw [dite_eq_left hj]
    have he : (⟨j.val,by omega⟩ : Fin (L+1)) = i ↔
        j = Fin.castLE (Nat.add_le_add_right h 1) i := by
      constructor <;> intro hh <;> apply Fin.ext
      · exact congrArg (fun k : Fin (L+1) => k.val) hh
      · exact congrArg (fun k : Fin (Q+1) => k.val) hh
    simp only [Pi.single_apply,he]
  · rw [dite_eq_right hj]
    have he : j ≠ Fin.castLE (Nat.add_le_add_right h 1) i := by
      intro hh
      have hv := congrArg (fun k : Fin (Q+1) => k.val) hh
      have := i.isLt
      simp only [Fin.val_castLE] at hv
      omega
    simp [he]

theorem fockInclusion_create (L Q : ℕ) (h : L ≤ Q) (i : Fin (L+1)) (x : Space L) :
    fockInclusion L Q h (create i x) =
      create (Fin.castLE (Nat.add_le_add_right h 1) i) (fockInclusion L Q h x) := by
  change ExteriorAlgebra.map (modeInclusion L Q h) (ExteriorAlgebra.ι ℂ (mode i) * x) = _
  rw [map_mul,ExteriorAlgebra.map_apply_ι,modeInclusion_mode]
  rfl

theorem contraction_map_between (L Q : ℕ) (f : Orbital L →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space L) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul,ExteriorAlgebra.map_apply_ι,CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply,map_sub,map_smul,hx]

theorem fockInclusion_annihilate (L Q : ℕ) (h : L ≤ Q) (i : Fin (L+1)) (x : Space L) :
    annihilate (Fin.castLE (Nat.add_le_add_right h 1) i) (fockInclusion L Q h x) =
      fockInclusion L Q h (annihilate i x) := by
  unfold annihilate fockInclusion
  rw [contraction_map_between]
  have hp : (LinearMap.proj (Fin.castLE (Nat.add_le_add_right h 1) i)).comp
      (modeInclusion L Q h) = LinearMap.proj i := by
    apply LinearMap.ext
    intro v
    change (if hj : i.val ≤ L then v ⟨i.val,by omega⟩ else 0) = v i
    rw [dite_eq_left (show i.val ≤ L by omega)]
  rw [hp]

theorem fockInclusion_annihilate_high (L Q : ℕ) (h : L ≤ Q) (i : Fin (Q+1))
    (hi : L < i.val) (x : Space L) :
    annihilate i (fockInclusion L Q h x) = 0 := by
  unfold annihilate fockInclusion
  rw [contraction_map_between]
  have he : (LinearMap.proj i).comp (modeInclusion L Q h) = 0 := by
    ext v
    simp [modeInclusion,show ¬i.val ≤ L by omega]
  rw [he]
  simp

theorem fockInclusion_occupation (L Q : ℕ) (h : L ≤ Q) (A : Finset (Fin (L+1))) :
    fockInclusion L Q h (occupationBasis L A) =
      occupationBasis Q (includedOccupations L Q h A) := by
  let S : Set.powersetCard (Fin (L+1)) A.card := ⟨A,rfl⟩
  let e := (Set.powersetCard.ofFinEmbEquiv.symm S).trans
    (Fin.castLEOrderEmb (Nat.add_le_add_right h 1))
  let T : Set.powersetCard (Fin (Q+1)) A.card := Set.powersetCard.ofFinEmbEquiv e
  have hT : T.val = includedOccupations L Q h A := by
    ext j
    change j ∈ Set.powersetCard.ofFinEmbEquiv e ↔ _
    rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
    simp only [Set.mem_range,includedOccupations,Finset.mem_map]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨Set.powersetCard.ofFinEmbEquiv.symm S i,?_,rfl⟩
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨i,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S i).mpr hi
      exact ⟨a,congrArg (Fin.castLE (Nat.add_le_add_right h 1)) ha⟩
  change fockInclusion L Q h ((Pi.basisFun ℂ (Fin (L+1))).ExteriorAlgebra S.val) = _
  rw [← hT]
  change ExteriorAlgebra.map (modeInclusion L Q h)
    ((Pi.basisFun ℂ (Fin (L+1))).ExteriorAlgebra S.val) =
      (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra T.val
  rw [ExteriorAlgebra.basis_apply_powersetCard,ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.map_apply_ιMulti]
  have he : Set.powersetCard.ofFinEmbEquiv.symm T = e :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply e
  rw [he]
  congr 1
  funext i
  simp only [Function.comp_apply,Pi.basisFun_apply]
  change modeInclusion L Q h (mode (Set.powersetCard.ofFinEmbEquiv.symm S i)) =
    mode (Fin.castLE (Nat.add_le_add_right h 1) (Set.powersetCard.ofFinEmbEquiv.symm S i))
  exact modeInclusion_mode L Q h (Set.powersetCard.ofFinEmbEquiv.symm S i)

theorem includedOccupations_injective (L Q : ℕ) (h : L ≤ Q) :
    Function.Injective (includedOccupations L Q h) := Finset.map_injective _

theorem fockInclusion_inner (L Q : ℕ) (h : L ≤ Q) (x y : Space L) :
    occupationInner Q (fockInclusion L Q h x) (fockInclusion L Q h y) =
      occupationInner L x y := by
  have hb (A B : Finset (Fin (L+1))) :
      occupationInner Q (fockInclusion L Q h (occupationBasis L A))
        (fockInclusion L Q h (occupationBasis L B)) =
          occupationInner L (occupationBasis L A) (occupationBasis L B) := by
    rw [fockInclusion_occupation,fockInclusion_occupation,occupationInner_basis,occupationInner_basis]
    simp only [(includedOccupations_injective L Q h).eq_iff]
  conv_lhs => rw [← (occupationBasis L).sum_repr x,← (occupationBasis L).sum_repr y]
  conv_rhs => rw [← (occupationBasis L).sum_repr x,← (occupationBasis L).sum_repr y]
  simp only [map_sum,map_smul,occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,hb]

theorem fockInclusion_normSq (L Q : ℕ) (h : L ≤ Q) (x : Space L) :
    occupationNormSq Q (fockInclusion L Q h x) = occupationNormSq L x := by
  have hi := fockInclusion_inner L Q h x x
  rw [occupationInner_self,occupationInner_self] at hi
  exact Complex.ofReal_injective hi

end Laughlin.Fock

end OAI
