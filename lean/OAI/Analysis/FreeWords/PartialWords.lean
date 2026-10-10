import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryAlgebra
import OAI.Analysis.FreeWords.PartialUnitaryNorm
import OAI.Analysis.FreeWords.TraceL2Convergence

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

open Filter Topology

noncomputable section

structure PatchingWord (A : Type*) where
  left : A
  first : ℤ
  middle : List (A × ℤ)
  right : A

namespace PatchingWord

variable {A : Type*} [Ring A]

def tailValue (u : ℤ → A) (s : List (A × ℤ)) : A :=
  (s.map (fun z => z.1*u z.2)).prod

def value (w : PatchingWord A) (u : ℤ → A) : A :=
  w.left*u w.first*tailValue u w.middle*w.right

def length (w : PatchingWord A) : ℕ := 1+w.middle.length

@[simp] theorem tailValue_nil (u : ℤ → A) : tailValue u []=1 := rfl

@[simp] theorem tailValue_cons (u : ℤ → A) (z : A × ℤ) (s : List (A × ℤ)) :
    tailValue u (z::s)=z.1*u z.2*tailValue u s := rfl

@[simp] theorem value_zero (w : PatchingWord A) : w.value (fun _ => 0)=0 := by
  simp [value]

theorem tailValue_append (u : ℤ → A) (s t : List (A × ℤ)) :
    tailValue u (s++t)=tailValue u s*tailValue u t := by
  simp only [tailValue,List.map_append,List.prod_append]

end PatchingWord

namespace PatchingWord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance partialWordsConcreteOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance partialWordsConcretePreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance partialWordsConcreteLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance partialWordsConcreteSOR : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem concrete_norm_one_le : ‖(1:ConcreteAlgebra M)‖≤1 := by
  have h := CStarRing.norm_star_mul_self (x := (1:ConcreteAlgebra M))
  simp only [star_one,mul_one] at h
  nlinarith [norm_nonneg (1:ConcreteAlgebra M)]

theorem norm_tailValue_le (v : PartialUnitary (ConcreteAlgebra M))
    (s : List (ConcreteAlgebra M × ℤ)) :
    ‖tailValue v.power s‖ ≤ (s.map (fun z => ‖z.1‖)).prod := by
  induction s with
  | nil => simpa only [tailValue_nil,List.map_nil,List.prod_nil] using (concrete_norm_one_le (M := M))
  | cons z s ih =>
    simp only [tailValue_cons,List.map_cons,List.prod_cons]
    calc
      _ ≤ ‖z.1*v.power z.2‖*‖tailValue v.power s‖ := norm_mul_le _ _
      _ ≤ (‖z.1‖*1)*(s.map (fun z => ‖z.1‖)).prod :=
        mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (v.norm_power_le_one _) (norm_nonneg _)))
          ih (norm_nonneg _) (mul_nonneg (norm_nonneg _) zero_le_one)
      _ = _ := by rw [mul_one]

theorem tendsto_tailValue {I : Type*} {l : Filter I}
    {f : I → PartialUnitary (ConcreteAlgebra M)} {v : PartialUnitary (ConcreteAlgebra M)}
    (hf : ∀ k, Tendsto (fun i => gnsVector (tracePositive τ) ((f i).power k)) l
      (𝓝 (gnsVector (tracePositive τ) (v.power k))))
    (s : List (ConcreteAlgebra M × ℤ)) :
    Tendsto (fun i => gnsVector (tracePositive τ) (tailValue (f i).power s)) l
      (𝓝 (gnsVector (tracePositive τ) (tailValue v.power s))) := by
  induction s with
  | nil => exact tendsto_const_nhds
  | cons z s ih =>
    simp only [tailValue_cons]
    apply tendsto_gns_mul τ ‖z.1‖ (norm_nonneg _) ?_ ?_ ih
    · intro i
      simpa only [mul_one] using (norm_mul_le z.1 ((f i).power z.2)).trans
        (mul_le_mul_of_nonneg_left ((f i).norm_power_le_one z.2) (norm_nonneg z.1))
    · exact tendsto_gns_mul τ ‖z.1‖ (norm_nonneg _) (fun _ => le_rfl)
        tendsto_const_nhds (hf z.2)

theorem tendsto_value {I : Type*} {l : Filter I}
    {f : I → PartialUnitary (ConcreteAlgebra M)} {v : PartialUnitary (ConcreteAlgebra M)}
    (hf : ∀ k, Tendsto (fun i => gnsVector (tracePositive τ) ((f i).power k)) l
      (𝓝 (gnsVector (tracePositive τ) (v.power k)))) (w : PatchingWord (ConcreteAlgebra M)) :
    Tendsto (fun i => τ.map (w.value (f i).power)) l (𝓝 (τ.map (w.value v.power))) := by
  apply tendsto_gns_trace τ
  have h₁ := tendsto_gns_mul τ ‖w.left‖ (norm_nonneg _) (fun (_:I) => le_rfl)
    tendsto_const_nhds (hf w.first)
  have hb (i:I) : ‖w.left*(f i).power w.first‖≤‖w.left‖ := by
    simpa only [mul_one] using (norm_mul_le w.left ((f i).power w.first)).trans
      (mul_le_mul_of_nonneg_left ((f i).norm_power_le_one w.first) (norm_nonneg w.left))
  have h₂ := tendsto_gns_mul τ ‖w.left‖ (norm_nonneg _) hb h₁ (tendsto_tailValue τ hf w.middle)
  have hp : 0≤(w.middle.map (fun z => ‖z.1‖)).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg _
  exact tendsto_gns_mul τ (‖w.left‖*(w.middle.map (fun z => ‖z.1‖)).prod)
    (mul_nonneg (norm_nonneg _) hp)
    (fun i => (norm_mul_le _ _).trans (mul_le_mul (hb i) (norm_tailValue_le (f i) w.middle)
      (norm_nonneg _) (norm_nonneg _))) h₂ tendsto_const_nhds

end PatchingWord

end

end KKLocalPatching
end

end OAI
