import OAI.Algebra.Finitistic.Rectification.ColumnComplex

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace ExternalTensor.Section4
universe u
variable {k : Type u} [Field k]
variable {C : Type u} [Category C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]

/-- The concrete column/map interface. No composite or null-homotopy is assumed.
The three equations are path naturality, the algebra relations, and the chosen
relation homotopies after column induction. -/
structure AssemblyData where
  V₀ : C
  V₁ : C
  V₂ : C
  U : A → C
  V : J → C
  W : R → C
  pa₀ : ∀ a, U a ⟶ V₀
  pa₁ : ∀ a, U a ⟶ V₁
  pb₁ : ∀ b, V b ⟶ V₁
  pb₂ : ∀ b, V b ⟶ V₂
  qa : ∀ relation arrow, J → (W relation ⟶ U arrow)
  qb : ∀ relation, A → ∀ arrow, W relation ⟶ V arrow
  rel : ∀ r, W r ⟶ V₂
  middle : ∀ r a b, qa r a b ≫ pa₁ a = qb r a b ≫ pb₁ b
  first : ∀ r, ∑ a, ∑ b, qa r a b ≫ pa₀ a = 0
  last : ∀ r, ∑ a, ∑ b, qb r a b ≫ pb₂ b = rel r

namespace AssemblyData
variable (s : AssemblyData (C := C) (A := A) (J := J) (R := R))
abbrev L₀ := s.V₀ ⊞ (s.V₁ ⊞ s.V₂)
abbrev L₁ := (⨁ s.U) ⊞ (⨁ s.V)
abbrev L₂ := ⨁ s.W
abbrev in₀ : s.V₀ ⟶ s.L₀ := biprod.inl
abbrev in₁ : s.V₁ ⟶ s.L₀ := biprod.inl ≫ biprod.inr
abbrev in₂ : s.V₂ ⟶ s.L₀ := biprod.inr ≫ biprod.inr

def p : s.L₁ ⟶ s.L₀ :=
  biprod.desc
    (biproduct.desc fun a => s.pa₀ a ≫ s.in₀ - s.pa₁ a ≫ s.in₁)
    (biproduct.desc fun b => s.pb₁ b ≫ s.in₁ - s.pb₂ b ≫ s.in₂)

def q : s.L₂ ⟶ s.L₁ :=
  biproduct.desc fun r => ∑ a, ∑ b,
    (s.qa r a b ≫ biproduct.ι s.U a ≫ biprod.inl +
     s.qb r a b ≫ biproduct.ι s.V b ≫ biprod.inr)

/-- The complete cancellation in Section 4, including the minus sign. -/
theorem composite : s.q ≫ s.p =
    -(biproduct.desc fun r => s.rel r ≫ s.in₂) := by
  apply biproduct.hom_ext'
  intro r
  simp only [q, biproduct.ι_desc_assoc, Preadditive.comp_neg,
    biproduct.ι_desc]
  simp only [Preadditive.sum_comp, Preadditive.add_comp, Category.assoc, p,
    biprod.inl_desc, biprod.inr_desc, biproduct.ι_desc, Preadditive.comp_sub,
    ]
  simp only [← Category.assoc, s.middle]
  simp only [Category.assoc]
  have cancel (a : A) (b : J) :
      s.qa r a b ≫ s.pa₀ a ≫ s.in₀ - s.qb r a b ≫ s.pb₁ b ≫ s.in₁ +
      (s.qb r a b ≫ s.pb₁ b ≫ s.in₁ - s.qb r a b ≫ s.pb₂ b ≫ s.in₂) =
      s.qa r a b ≫ s.pa₀ a ≫ s.in₀ - s.qb r a b ≫ s.pb₂ b ≫ s.in₂ := by abel
  simp_rw [cancel, Finset.sum_sub_distrib]
  have hf := congrArg (fun z => z ≫ s.in₀) (s.first r)
  have hl := congrArg (fun z => z ≫ s.in₂) (s.last r)
  simp only [Preadditive.sum_comp, Category.assoc, zero_comp] at hf hl
  rw [hf, hl]
  simp

/-- A componentwise specified finite sum of homotopies. -/
def sumHomotopy {E : Type*} [Category E] [Preadditive E]
    {X Y : CochainComplex E ℤ} {I : Type} [Fintype I]
    (f : I → (X ⟶ Y)) (H : ∀ i, Homotopy (f i) 0) :
    Homotopy (∑ i, f i) 0 where
  hom n m := ∑ i, (H i).hom n m
  zero n m h := by simp [fun i => (H i).zero n m h]
  comm n := by
    change Hom.fAddMonoidHom n (∑ i, f i) = _
    rw [map_sum]
    change (∑ i, (f i).f n) = _
    calc
      _ = ∑ i, (dNext n (H i).hom + prevD n (H i).hom + (0 : X ⟶ Y).f n) :=
        Finset.sum_congr rfl (fun i _ => (H i).comm n)
      _ = _ := by
        simp [dNext, prevD, Preadditive.comp_sum, Preadditive.sum_comp,
          Finset.sum_add_distrib]
end AssemblyData
end ExternalTensor.Section4

end

end OAI
