import Mathlib
import OAI.Algebra.FiniteTensor.CompatibleCharts

namespace OAI

/-! Positive-characteristic tensor obstruction and exact formal parametrization conditions. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
open FrobeniusTruncation FiniteCoordinates
attribute [local instance] parameterCharP
universe u
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Fact p.Prime] [Invertible (2 : K)]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

include p in
 

theorem formal_positive_obstruction {d c : ℕ}
    (e : ((i : Fin (n+1)) × σ i) ≃ Fin d ⊕ Fin c)
    (F b : ∀ i,MvPowerSeries (σ i) K) (active : Finset (Fin (n+1)))
    (hb : ∀ i,i∉active → b i=0) (hA : 5≤active.card)
    (H0 : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) K)
    (G : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin c) K)
    (H : (Fin 3 ↪ Fin (n+1)) → ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) (T K 3))
    (hH0z : ∀ i,MvPowerSeries.constantCoeff (H0 i)=0)
    (hGz : ∀ i,MvPowerSeries.constantCoeff (G i)=0)
    (hH : ∀ q i,MvPowerSeries.map (augmentation K 3) (H q i)=H0 i)
    (hHL : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (H0 i))))
    (hGR : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))))
    (hcomp : IsCompl (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (H0 i))).range
      (Matrix.mulVecLin (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))).range)
    (hL0 : MvPowerSeries.subst H0 (formalSigmaPotential K σ F)=0)
    (hR : MvPowerSeries.subst G (formalSigmaPotential K σ F)=0)
    (htripR : ∀ s : Finset (Fin (n+1)), s⊆active → s.card=3 →
      MvPowerSeries.subst G (formalSigmaSelected K σ b s)∈Ideal.span
        (Set.range (fun i => MvPowerSeries.subst G
          (MvPowerSeries.pderiv i (formalSigmaPotential K σ F)))))
    (hL : ∀ q : Fin 3 ↪ Fin (n+1), (∀ j,q j∈active) →
      MvPowerSeries.subst (H q) (formalSigmaDeformed K σ F b q)=0)
    (htripL : ∀ q : Fin 3 ↪ Fin (n+1), (∀ j,q j∈active) →
      MvPowerSeries.C (t K 3 0*t K 3 1*t K 3 2)∈Ideal.span
        (Set.range (fun i => MvPowerSeries.subst (H q)
          (MvPowerSeries.pderiv i (formalSigmaDeformed K σ F b q))))) : False := by
  classical
  let : CharP (T K 3) p := parameterCharP K 3 p
  let : Algebra K (T K 3) := inferInstance
  obtain ⟨q0,hq0L,hq0R,hqs⟩ := compatible_graph_charts K _ (Fin d) (Fin c) p
    (Fin 3) (fun _ => 2) (fun _ => by decide) (fun _ => (Fact.out : p.Prime).two_le)
    e H0 G hH0z hGz hHL hGR hcomp
  have hHc (q : Fin 3 ↪ Fin (n+1)) (i) :
      MvPowerSeries.map (constantMap K (Fin 3) (fun _ => 2) (fun _ => by decide)).toRingHom
        (H q i)=H0 i := by
    rw [constantMap_parameters]
    exact hH q i
  choose qL hqLL hqSS using fun q => hqs (H q) (hHc q)
  let r := (e.trans finSumFinEquiv).trans (finCongr (Nat.add_comm d c))
  have hH0sub := MvPowerSeries.hasSubst_of_constantCoeff_zero hH0z
  have hGsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hGz
  have hHsub (q : Fin 3 ↪ Fin (n+1)) : MvPowerSeries.HasSubst (H q) := by
    apply parameter_hasSubst
    intro i
    exact (congrArg MvPowerSeries.constantCoeff (hH q i)).trans (hH0z i)
  apply finite_chart_obstruction K p σ r e q0 qL
    (fun i => formalEval K (σ i) p (F i)) (fun i => formalEval K (σ i) p (b i))
    active (fun i hi => by rw [hb i hi,map_zero]) hA
  · rw [←formalSigmaPotential_eval]
    exact graph_zero K _ (Fin d) (Fin c) p (Fact.out : p.Prime).pos e q0
      H0 hH0sub hq0L _ hL0
  · rw [←formalSigmaPotential_eval]
    exact graph_zero K _ (Fin c) (Fin d) p (Fact.out : p.Prime).pos
      (e.trans (Equiv.sumComm _ _)) q0 G hGsub hq0R _ hR
  · intro s hs hc
    rw [←formalSigmaSelected_eval]
    simp only [←formalSigmaPotential_eval]
    exact graph_gradient K K _ (Fin c) (Fin d) p (Fact.out : p.Prime).pos
      (e.trans (Equiv.sumComm _ _)) q0 G hGsub hq0R
      (formalSigmaPotential K σ F) (formalSigmaSelected K σ b s) (htripR s hs hc)
  · intro q hq a
    have hh := hqSS q a
    rw [constantMap_parameters] at hh
    exact hh
  · intro q hq
    rw [←formalSigmaDeformed_eval]
    exact graph_zero (T K 3) ((i : Fin (n+1)) × σ i) (Fin d) (Fin c)
      p (Fact.out : p.Prime).pos
      e (qL q) (H q) (hHsub q) (hqLL q) _ (hL q hq)
  · intro q hq
    rw [←formalSigmaDeformed_eval]
    have ht : MvPowerSeries.subst (H q)
        (MvPowerSeries.C (t K 3 0*t K 3 1*t K 3 2))∈Ideal.span
        (Set.range (fun i => MvPowerSeries.subst (H q)
          (MvPowerSeries.pderiv i (formalSigmaDeformed K σ F b q)))) := by
      simpa only [MvPowerSeries.subst_C] using htripL q hq
    have hh := @graph_gradient K (T K 3) ((i : Fin (n+1)) × σ i) (Fin d) (Fin c)
      inferInstance inferInstance (inferInstance : Algebra K (T K 3))
      inferInstance inferInstance inferInstance p (parameterCharP K 3 p) (Fact.out : p.Prime).pos
      e (qL q) (H q) (hHsub q) (hqLL q) (formalSigmaDeformed K σ F b q)
      (MvPowerSeries.C (t K 3 0*t K 3 1*t K 3 2)) ht
    erw [show nilEval (T K 3) (coord (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
        (fun j => ⟨p,coord_pow _ _ _ j⟩) (MvPowerSeries.C (t K 3 0*t K 3 1*t K 3 2))=
      algebraMap (T K 3) (Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
        (t K 3 0*t K 3 1*t K 3 2) from (nilEval (T K 3) _ _).commutes _] at hh
    exact hh

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
universe u
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Fact p.Prime] [Invertible (2 : K)]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

include p in
 

theorem formal_active_obstruction {d c m : ℕ}
    (e : ((i : Fin (n+1)) × σ i) ≃ Fin d ⊕ Fin c)
    (hm : 5 ≤ m) (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin (n+1)) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (H : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin d) (T K m))
    (G : ((i : Fin (n+1)) × σ i) → MvPowerSeries (Fin c) K)
    (hHz : ∀ i,MvPowerSeries.constantCoeff (H i)∈parameterIdeal K m)
    (hGz : ∀ i,MvPowerSeries.constantCoeff (G i)=0)
    (hHL : Function.Injective (Matrix.mulVecLin
      (fun i j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))))
    (hGR : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))))
    (hcomp : IsCompl (Matrix.mulVecLin
      (fun i j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))).range
      (Matrix.mulVecLin (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))).range)
    (hL : MvPowerSeries.subst H (formalActiveDeformed K σ m F active b)=0)
    (hR : MvPowerSeries.subst G (formalSigmaPotential K σ F)=0)
    (htripL : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.C (t K m i*t K m j*t K m k)∈Ideal.span
        (Set.range (fun x => MvPowerSeries.subst H
          (MvPowerSeries.pderiv x (formalActiveDeformed K σ m F active b)))))
    (htripR : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.subst G
        (MvPowerSeries.rename (Sigma.mk (active i)) (b i)*
          MvPowerSeries.rename (Sigma.mk (active j)) (b j)*
          MvPowerSeries.rename (Sigma.mk (active k)) (b k))∈Ideal.span
            (Set.range (fun x => MvPowerSeries.subst G
              (MvPowerSeries.pderiv x (formalSigmaPotential K σ F))))) : False := by
  classical
  let A : Finset (Fin (n+1)) := Finset.univ.map active
  let H0 := fun i => MvPowerSeries.map (augmentation K m) (H i)
  let Hq := fun (q : Fin 3 ↪ Fin (n+1)) i =>
    MvPowerSeries.map (parameterSelector K m active q).toRingHom (H i)
  have hHsub : MvPowerSeries.HasSubst H :=
    parameter_hasSubst K m H (fun i => augmentation_zero_of_mem K m _ (hHz i))
  have hmem (i : Fin (n+1)) : i∈A ↔ i∈Set.range active := by
    simp only [A,Finset.mem_map,Finset.mem_univ,true_and,Set.mem_range]
  apply formal_positive_obstruction K p σ e F (activeExtension active b) A
    (fun i hi => activeExtension_other (A:=fun i => MvPowerSeries (σ i) K)
      active b i (fun h => hi ((hmem i).mpr h)))
    (by simpa only [A,Finset.card_map,Finset.card_univ,Fintype.card_fin] using hm) H0 G Hq
  · intro i
    change MvPowerSeries.constantCoeff (MvPowerSeries.map (augmentation K m) (H i))=0
    rw [MvPowerSeries.constantCoeff_map]
    exact augmentation_zero_of_mem K m _ (hHz i)
  · exact hGz
  · intro q i
    exact augmentation_selector_graph K m active q H i
  · simpa only [H0,MvPowerSeries.coeff_map] using hHL
  · exact hGR
  · simpa only [H0,MvPowerSeries.coeff_map] using hcomp
  · exact central_graph_zero K σ m F active b H hHsub hL
  · exact hR
  · intro s hs hs3
    exact active_right_triples K σ m F active b G htripR s
      (fun i hi => (hmem i).mp (hs hi)) hs3
  · intro q _
    exact selector_graph_zero K σ m F active b H hHsub hL q
  · intro q hq
    exact selector_graph_triple K σ m F active b H hHsub htripL q
      (fun j => (hmem (q j)).mp (hq j))

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
universe u
variable (K : Type*) [Field K] {l : ℕ} (σ : Fin l → Type u)
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

def formalAnyPotential (F : ∀ i,MvPowerSeries (σ i) K) :
    MvPowerSeries ((i : Fin l) × σ i) K :=
  ∑ i,MvPowerSeries.rename (Sigma.mk i) (F i)

def formalAnyDeformed (m : ℕ) (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin l) (b : ∀ j,MvPowerSeries (σ (active j)) K) :
    MvPowerSeries ((i : Fin l) × σ i) (T K m) :=
  MvPowerSeries.map (algebraMap K (T K m)) (formalAnyPotential K σ F) +
    ∑ j,MvPowerSeries.C (t K m j)*MvPowerSeries.map (algebraMap K (T K m))
      (MvPowerSeries.rename (Sigma.mk (active j)) (b j))

variable (p : ℕ) [CharP K p] [Fact p.Prime] [Invertible (2 : K)]

include p in
 
theorem formal_active_obstruction_any {d c m : ℕ}
    (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c)
    (hm : 5 ≤ m) (F : ∀ i,MvPowerSeries (σ i) K)
    (active : Fin m ↪ Fin l) (b : ∀ j,MvPowerSeries (σ (active j)) K)
    (H : ((i : Fin l) × σ i) → MvPowerSeries (Fin d) (T K m))
    (G : ((i : Fin l) × σ i) → MvPowerSeries (Fin c) K)
    (hHz : ∀ i,MvPowerSeries.constantCoeff (H i)∈parameterIdeal K m)
    (hGz : ∀ i,MvPowerSeries.constantCoeff (G i)=0)
    (hHL : Function.Injective (Matrix.mulVecLin
      (fun i j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))))
    (hGR : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))))
    (hcomp : IsCompl (Matrix.mulVecLin
      (fun i j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (H i)))).range
      (Matrix.mulVecLin (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))).range)
    (hL : MvPowerSeries.subst H (formalAnyDeformed K σ m F active b)=0)
    (hR : MvPowerSeries.subst G (formalAnyPotential K σ F)=0)
    (htripL : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.C (t K m i*t K m j*t K m k)∈Ideal.span
        (Set.range (fun x => MvPowerSeries.subst H
          (MvPowerSeries.pderiv x (formalAnyDeformed K σ m F active b)))))
    (htripR : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
      MvPowerSeries.subst G
        (MvPowerSeries.rename (Sigma.mk (active i)) (b i)*
          MvPowerSeries.rename (Sigma.mk (active j)) (b j)*
          MvPowerSeries.rename (Sigma.mk (active k)) (b k))∈Ideal.span
            (Set.range (fun x => MvPowerSeries.subst G
              (MvPowerSeries.pderiv x (formalAnyPotential K σ F))))) : False := by
  cases l with
  | zero => exact Fin.elim0 (active ⟨0, by omega⟩)
  | succ n =>
    exact formal_active_obstruction K p σ e hm F active b H G hHz hGz hHL hGR hcomp
      hL hR htripL htripR

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor

open scoped BigOperators

variable (K : Type*) [Field K] (m : ℕ)

 
 
abbrev Coordinates (n : Fin (2*m) → ℕ) := (i : Fin (2*m)) × Fin (n i)

abbrev N (n : Fin (2*m) → ℕ) := Fintype.card (Coordinates m n)

 
def includeBlock {n : Fin (2*m) → ℕ} (i : Fin (2*m))
    (F : MvPowerSeries (Fin (n i)) K) : MvPowerSeries (Coordinates m n) K :=
  MvPowerSeries.rename (fun j => (⟨i, j⟩ : Coordinates m n)) F

 
structure Germs (n : Fin (2*m) → ℕ) (active : Fin m ↪ Fin (2*m)) where
  F : (i : Fin (2*m)) → MvPowerSeries (Fin (n i)) K
  b : (i : Fin m) → MvPowerSeries (Fin (n (active i))) K
  F_algebraic : ∀ i, IsAlgebraic (MvPolynomial (Fin (n i)) K) (F i)
  b_algebraic : ∀ i, IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (b i)
  F_zero : ∀ i, MvPowerSeries.constantCoeff (F i) = 0
  b_zero : ∀ i, MvPowerSeries.constantCoeff (b i) = 0

variable {K m}

def Germs.S₀ {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) : MvPowerSeries (Coordinates m n) K :=
  ∑ i, includeBlock K m i (g.F i)

def Germs.B {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) (i : Fin m) : MvPowerSeries (Coordinates m n) K :=
  includeBlock K m (active i) (g.b i)

def Germs.Sₜ {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) : MvPowerSeries (Coordinates m n) (T K m) :=
  MvPowerSeries.map (algebraMap K (T K m)) g.S₀ +
    ∑ i, MvPowerSeries.C (t K m i) * MvPowerSeries.map (algebraMap K (T K m)) (g.B i)

variable (K m)

 

structure Parametrizations (n : Fin (2*m) → ℕ) (d : ℕ) where
  dimension_le : d ≤ N m n
  HL : Coordinates m n → MvPowerSeries (Fin d) (T K m)
  HR : Coordinates m n → MvPowerSeries (Fin (N m n - d)) K
  HL_zero : ∀ ν, MvPowerSeries.constantCoeff (HL ν) ∈ parameterIdeal K m
  HR_zero : ∀ ν, MvPowerSeries.constantCoeff (HR ν) = 0

variable {K m}

def Parametrizations.leftTangent {n : Fin (2*m) → ℕ} {d : ℕ}
    (h : Parametrizations K m n d) : (Fin d → K) →ₗ[K] Coordinates m n → K :=
  Matrix.mulVecLin (fun ν j => augmentation K m (MvPowerSeries.coeff (Finsupp.single j 1) (h.HL ν)))

def Parametrizations.rightTangent {n : Fin (2*m) → ℕ} {d : ℕ}
    (h : Parametrizations K m n d) : (Fin (N m n - d) → K) →ₗ[K] Coordinates m n → K :=
  Matrix.mulVecLin (fun ν j => MvPowerSeries.coeff (Finsupp.single j 1) (h.HR ν))

def Germs.leftJacobian {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) {d : ℕ} (h : Parametrizations K m n d) :
    Ideal (MvPowerSeries (Fin d) (T K m)) :=
  Ideal.span (Set.range (fun ν =>
    MvPowerSeries.subst h.HL (MvPowerSeries.pderiv ν g.Sₜ)))

def Germs.rightJacobian {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) {d : ℕ} (h : Parametrizations K m n d) :
    Ideal (MvPowerSeries (Fin (N m n - d)) K) :=
  Ideal.span (Set.range (fun ν =>
    MvPowerSeries.subst h.HR (MvPowerSeries.pderiv ν g.S₀)))

 

structure TensorConditions {n : Fin (2*m) → ℕ} {active : Fin m ↪ Fin (2*m)}
    (g : Germs K m n active) {d : ℕ} (h : Parametrizations K m n d) : Prop where
  left_injective : Function.Injective h.leftTangent
  right_injective : Function.Injective h.rightTangent
  complementary : IsCompl (LinearMap.range h.leftTangent) (LinearMap.range h.rightTangent)
  left_vanishing : MvPowerSeries.subst h.HL g.Sₜ = 0
  right_vanishing : MvPowerSeries.subst h.HR g.S₀ = 0
  left_triple : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k →
    MvPowerSeries.C (t K m i * t K m j * t K m k) ∈ g.leftJacobian h
  right_triple : ∀ i j k : Fin m, i ≠ j → i ≠ k → j ≠ k →
    MvPowerSeries.subst h.HR (g.B i * g.B j * g.B k) ∈ g.rightJacobian h

 
def FiniteTensorObstruction : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : CharZero K) (m : ℕ), 5 ≤ m →
    ∀ (n : Fin (2*m) → ℕ) (active : Fin m ↪ Fin (2*m))
      (g : Germs K m n active) (d : ℕ) (h : Parametrizations K m n d),
      ¬ TensorConditions g h

end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped BigOperators
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Fact p.Prime]

include p in
 

theorem positiveTensorObstruction (hp : p ≠ 2) (m : ℕ) (hm : 5 ≤ m)
    (n : Fin (2*m) → ℕ) (active : Fin m ↪ Fin (2*m))
    (g : Germs K m n active) (d : ℕ) (h : Parametrizations K m n d) :
    ¬ TensorConditions g h := by
  classical
  intro hc
  have h2 : (2 : K) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let e : Coordinates m n ≃ Fin d ⊕ Fin (N m n-d) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_sum,Fintype.card_fin]
      exact (Nat.add_sub_cancel' h.dimension_le).symm)
  exact TruncatedForms.formal_active_obstruction_any K (fun i => Fin (n i)) p e
    hm g.F active g.b h.HL h.HR h.HL_zero h.HR_zero hc.left_injective
    hc.right_injective hc.complementary hc.left_vanishing hc.right_vanishing
    hc.left_triple hc.right_triple

end
end PD4Tensor
end

end OAI
