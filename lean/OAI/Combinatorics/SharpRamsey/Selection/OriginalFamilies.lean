import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.NullFreeLaw
import OAI.Combinatorics.SharpRamsey.Execution.OriginalTargetLoss

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I : Type*} [Fintype I]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

abbrev OriginalChoice := {z // (familyLaw X Y).mass z≠0}

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma originalChoice_size (z : OriginalChoice X Y) (i : I) :
    MA i*exp (-κA i)/2≤((z.val.1 i).card:ℝ) ∧
    MB i*exp (-κB i)/2≤((z.val.2 i).card:ℝ) :=
  ⟨((familyLaw_support X Y z.val z.property).1 i).2.1,
   ((familyLaw_support X Y z.val z.property).2 i).2.1⟩

def originalFamily {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (z : OriginalChoice X Y) (i : I) : Original (K:=K) (V:=V) n b where
  A := z.val.2 i
  B := z.val.1 i
  nonemptyA := by
    apply card_pos.mp
    exact_mod_cast lt_of_lt_of_le (div_pos (mul_pos (hMB i) (exp_pos _)) (by norm_num) : 0<MB i*exp (-κB i)/2)
      (originalChoice_size X Y z i).2
  nonemptyB := by
    apply card_pos.mp
    exact_mod_cast lt_of_lt_of_le (div_pos (mul_pos (hMA i) (exp_pos _)) (by norm_num) : 0<MA i*exp (-κA i)/2)
      (originalChoice_size X Y z i).1
  product := by
    apply (hprod i).trans
    rw [mul_comm ((z.val.2 i).card:ℝ)]
    exact mul_le_mul (originalChoice_size X Y z i).1 (originalChoice_size X Y z i).2
      (div_nonneg (mul_nonneg (hMB i).le (exp_pos _).le) (by norm_num)) (by positivity)

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_density {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2)) (i j : I) :
    (∑ z,(familyLaw X Y).nullFree.mass z *
      density (originalFamily X Y hMA hMB hprod z i).B
        (originalFamily X Y hMA hMB hprod z j).A)≤
      (4*exp 1)*(4*exp 1)*((p i).prod (r j)).event
        (univ.filter (fun ay=>ay.1∈goodA i ∧ ay.2∈goodB j ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(familyLaw X Y).nullFree.mass z * density (z.val.1 i) (z.val.2 j))≤_
  rw [(familyLaw X Y).nullFree_integral (fun z=>density (z.1 i) (z.2 j))]
  exact familyLaw_incidence X Y i j (fun a y=>a.rep y.rep=0)

variable {Ω : Type*} [Fintype Ω]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma firstTargetDensity_mean (μ : Law Ω) (a : Ω→Projectivization K (Module.Dual K V))
    (G : Finset (Projectivization K (Module.Dual K V))) (T : Finset (Projectivization K V)) :
    (∑ ω,μ.mass ω*firstTargetDensity (a ω∈G) (a ω) T)=
      pairing (fun y=>if y∈G then (μ.map a).mass y else 0) (kernel T)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  rw [←μ.sum_map a (fun y=>firstTargetDensity (y∈G) y T)]
  unfold pairing firstTargetDensity
  apply sum_congr rfl
  intro y _
  by_cases hy : y∈G <;> simp [hy,mul_sum]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma secondTargetDensity_mean (μ : Law Ω) (c : Ω→Projectivization K V)
    (G : Finset (Projectivization K V)) (S : Finset (Projectivization K (Module.Dual K V))) :
    (∑ ω,μ.mass ω*secondTargetDensity (c ω∈G) (c ω) S)=
      pairing (kernel S) (fun x=>if x∈G then (μ.map c).mass x else 0)
        (fun y x=>if y.rep x.rep=0 then 1 else 0) := by
  rw [←μ.sum_map c (fun x=>secondTargetDensity (x∈G) x S),pairing_reverse]
  unfold pairing secondTargetDensity
  apply sum_congr rfl
  intro x _
  by_cases hx : x∈G <;> simp [hx,mul_sum]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_first_target {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (μ : Law Ω) (a : Ω→Projectivization K (Module.Dual K V))
    (G : Finset (Projectivization K (Module.Dual K V))) (j : I) :
    (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
      firstTargetDensity (a z.1∈G) (a z.1) (originalFamily X Y hMA hMB hprod z.2 j).A)≤
      (4*exp 1)*((μ.map a).prod (r j)).event
        (univ.filter (fun ay=>ay.1∈G ∧ ay.2∈goodB j ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
    firstTargetDensity (a z.1∈G) (a z.1) (z.2.val.2 j))≤_
  rw [μ.prod_sum_swap (familyLaw X Y).nullFree
    (fun ω z=>firstTargetDensity (a ω∈G) (a ω) (z.val.2 j))]
  simp_rw [firstTargetDensity_mean]
  rw [(familyLaw X Y).nullFree_integral (fun z=>pairing
    (fun y=>if y∈G then (μ.map a).mass y else 0) (kernel (z.2 j))
    (fun y x=>if y.rep x.rep=0 then 1 else 0))]
  simp_rw [pairing_reverse (fun y=>if y∈G then (μ.map a).mass y else 0)]
  have hh := familyLaw_second_target (μ.map a) G X Y j (fun y x=>x.rep y.rep=0)
  have he : ((r j).prod (μ.map a)).event
      (univ.filter (fun yx=>yx.1∈goodB j ∧ yx.2∈G ∧ yx.2.rep yx.1.rep=0))=
      ((μ.map a).prod (r j)).event
      (univ.filter (fun xy=>xy.1∈G ∧ xy.2∈goodB j ∧ xy.1.rep xy.2.rep=0)) := by
    rw [←good_pairing_eq_event (r j) (μ.map a) (goodB j) G (fun y x=>x.rep y.rep=0),
      ←good_pairing_eq_event (μ.map a) (r j) G (goodB j) (fun x y=>x.rep y.rep=0)]
    exact pairing_reverse _ _ _
  rw [he] at hh
  exact hh

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem originalFamily_second_target {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (μ : Law Ω) (c : Ω→Projectivization K V) (G : Finset (Projectivization K V)) (i : I) :
    (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
      secondTargetDensity (c z.1∈G) (c z.1) (originalFamily X Y hMA hMB hprod z.2 i).B)≤
      (4*exp 1)*((p i).prod (μ.map c)).event
        (univ.filter (fun ay=>ay.1∈goodA i ∧ ay.2∈G ∧ ay.1.rep ay.2.rep=0)) := by
  change (∑ z,(μ.prod (familyLaw X Y).nullFree).mass z *
    secondTargetDensity (c z.1∈G) (c z.1) (z.2.val.1 i))≤_
  rw [μ.prod_sum_swap (familyLaw X Y).nullFree
    (fun ω z=>secondTargetDensity (c ω∈G) (c ω) (z.val.1 i))]
  simp_rw [secondTargetDensity_mean]
  rw [(familyLaw X Y).nullFree_integral (fun z=>pairing (kernel (z.1 i))
    (fun x=>if x∈G then (μ.map c).mass x else 0)
    (fun y x=>if y.rep x.rep=0 then 1 else 0))]
  exact familyLaw_first_target (μ.map c) G X Y i (fun y x=>y.rep x.rep=0)

end
end SharpLogRamsey.ActualPivot

end

end OAI
