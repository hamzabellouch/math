import OAI.NumberTheory.DirichletL.Reflection.SectorIndependence

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_common_reflected_coefficients {α Q κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (γ : Q → Eisˣ → ℕ → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x u m, sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
        γ (sector x) u m) ∧
      ∀ x u m n b, sourceColumn (D x) s hc (hg x) (j x) (F.image (f x)) u m n b =
        β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let G := fun x => sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x))
  let B := fun x => sourceColumn (D x) s hc (hg x) (j x) (F.image (f x))
  have hG : G.FactorsThrough sector := by
    intro x y hxy
    funext u m
    exact sourceFrozenPhase_sector_independent (D x) (D y) s (hp x) (hg x) (hp y) (hg y)
      hN (hprimary x) (hprimary y) hbase (hmatrix x y hxy) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m
  have hB : B.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact sourceColumn_sector_independent (D x) (D y) s hc (hg x) (hg y) hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m n b
  obtain ⟨γ,hγ⟩ := (Function.factorsThrough_iff G).mp hG
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff B).mp hB
  refine ⟨γ,β,?_,?_⟩
  · intro x u m
    exact congrFun (congrFun (congrFun hγ x) u) m
  · intro x u m n b
    exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedProduct : Eis) (r P : α → Eis)
    (hprod : ∀ x, (∏ i, p x i) = fixedProduct*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧ (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧ (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
          γ (separateSector N (r x) (P x)) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (hg x) (j x) (F.image (f x)) u m n b =
          β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N fixedProduct (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_common_reflected_coefficients p N a c mode E s hp hc hg hN hprimary hbase
    j f hf hfixed hjfixed F sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI
