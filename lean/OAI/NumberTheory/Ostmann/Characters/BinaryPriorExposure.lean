import OAI.NumberTheory.Ostmann.Characters.BinaryExposureLeaves
import OAI.NumberTheory.Ostmann.Characters.PriorResidueDomination

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.BinaryPriorExposure
open Construction BinaryHaar BinaryExposure
attribute [local instance] Classical.propDecidable
variable {α β:Type*} [Fintype α] [Fintype β]

def mean (μ:List Bool→FinitePrior α) : (k:ℕ) → List Bool → (Leaves α k→ℝ) → ℝ
  | 0,p,F => (μ p).mean F
  | k+1,p,F => mean μ k (false::p) (fun x=>mean μ k (true::p) (fun y=>F (x,y)))

def map (f:List Bool→α→β) : (k:ℕ) → List Bool → Leaves α k → Leaves β k
  | 0,p,x => f p x
  | k+1,p,x => (map f k (false::p) x.1,map f k (true::p) x.2)

def cost (D:List Bool→NNReal) : ℕ → List Bool → NNReal
  | 0,p => D p
  | k+1,p => cost D k (false::p)*cost D k (true::p)

theorem mean_nonneg (μ:List Bool→FinitePrior α) (k:ℕ) (p:List Bool)
    (F:Leaves α k→ℝ) (hF:∀x,0≤F x) : 0≤ mean μ k p F := by
  induction k generalizing p with
  | zero => exact (μ p).mean_nonneg hF
  | succ k ih => exact ih _ _ (fun x=>ih _ _ (fun y=>hF (x,y)))

theorem mean_mono (μ:List Bool→FinitePrior α) (k:ℕ) (p:List Bool)
    (F G:Leaves α k→ℝ) (hFG:∀x,F x≤G x) : mean μ k p F≤ mean μ k p G := by
  induction k generalizing p with
  | zero => exact (μ p).mean_mono hFG
  | succ k ih => exact ih _ _ _ (fun x=>ih _ _ _ (fun y=>hFG (x,y)))

theorem mean_const_mul (μ:List Bool→FinitePrior α) (k:ℕ) (p:List Bool)
    (F:Leaves α k→ℝ) (c:ℝ) : mean μ k p (fun x=>c*F x)=c*mean μ k p F := by
  induction k generalizing p with
  | zero =>
    change (∑x,(μ p).mass x*(c*F x))=c*∑x,(μ p).mass x*F x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _=>by ring)
  | succ k ih =>
    change mean μ k (false::p) (fun x=>mean μ k (true::p) (fun y=>c*F (x,y)))=_
    simp_rw [ih]
    rfl

theorem mean_le_uniform (μ:List Bool→FinitePrior α) (f:List Bool→α→β)
    (D:List Bool→NNReal)
    (hf:∀p b,(pushForwardPrior (μ p) (f p)).mass b≤(D p:ℝ)/(Fintype.card β:ℝ))
    (k:ℕ) (p:List Bool) (F:Leaves β k→ℝ) (hF:∀x,0≤F x) :
    mean μ k p (fun x=>F (map f k p x))≤(cost D k p:ℝ)*avg F := by
  induction k generalizing p with
  | zero => exact mean_le_uniform_of_fiber_mass (μ p) (f p) (D p) (hf p) F hF
  | succ k ih =>
    change mean μ k (false::p) (fun x=>mean μ k (true::p)
      (fun y=>F (map f k (false::p) x,map f k (true::p) y))) ≤ _
    calc
      _ ≤ mean μ k (false::p) (fun x=>(cost D k (true::p):ℝ)*
          avg (fun y:Leaves β k=>F (map f k (false::p) x,y))) :=
        mean_mono _ _ _ _ _ (fun x=>ih _ _ (fun y=>hF (_,y)))
      _ = (cost D k (true::p):ℝ)*mean μ k (false::p)
          (fun x=>avg (fun y:Leaves β k=>F (map f k (false::p) x,y))) :=
        mean_const_mul _ _ _ _ _
      _ ≤ (cost D k (true::p):ℝ)*((cost D k (false::p):ℝ)*
          avg (fun x:Leaves β k=>avg (fun y:Leaves β k=>F (x,y)))) :=
        mul_le_mul_of_nonneg_left
          (ih _ _ (fun x=>avg_nonneg _ (fun y=>hF (x,y)))) (cost D k (true::p)).property
      _ = (cost D (k+1) p:ℝ)*avg F := by
        rw [← avg_prod]
        change _=((cost D k (false::p):ℝ)*(cost D k (true::p):ℝ))*avg F
        ring

theorem indicator_le_uniform (μ:List Bool→FinitePrior α) (f:List Bool→α→β)
    (D:List Bool→NNReal)
    (hf:∀p b,(pushForwardPrior (μ p) (f p)).mass b≤(D p:ℝ)/(Fintype.card β:ℝ))
    (k:ℕ) (p:List Bool) (P:Leaves β k→Prop) :
    mean μ k p (fun x=>if P (map f k p x) then 1 else 0) ≤
      (cost D k p:ℝ)*((Nat.card {x:Leaves β k // P x}:ℝ)/Nat.card (Leaves β k)) := by
  classical
  simpa only [avg_indicator] using mean_le_uniform μ f D hf k p
    (fun x=>if P x then 1 else 0) (fun x=>by split_ifs <;> norm_num)

end Ostmann.Characters.BinaryPriorExposure

end

end OAI
