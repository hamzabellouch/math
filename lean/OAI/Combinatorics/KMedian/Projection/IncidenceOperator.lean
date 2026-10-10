import Mathlib
import OAI.Combinatorics.KMedian.Expanders.Cloud
import OAI.Combinatorics.KMedian.Projection.Operator

namespace OAI

section Inline_PCPIncidenceOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b)=(f false+f true)/2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.sum_bool,Fintype.card_bool,Nat.cast_ofNat]
  ring

namespace PortGraph
variable {V D A B : Type} (G : PortGraph V D)
def incidenceEdge : (V × D) × Bool ≃ V × (D × Bool) where
  toFun p := let q := if p.2 then G.rotate p.1 else p.1; (q.1,(q.2,p.2))
  invFun p := (if p.2.2 then G.rotate (p.1,p.2.1) else (p.1,p.2.1),p.2.2)
  left_inv p := by
    rcases p with ⟨⟨v,d⟩,b⟩
    cases b
    · rfl
    · change (G.rotate (G.rotate (v,d)),true)=((v,d),true)
      rw [G.involutive (v,d)]
  right_inv p := by
    rcases p with ⟨v,d,b⟩
    cases b
    · rfl
    · change ((G.rotate (G.rotate (v,d))).1,((G.rotate (G.rotate (v,d))).2,true))=(v,d,true)
      rw [G.involutive (v,d)]

def incidence (π : (V × D) × Bool → A → B) : BiProjection (V × D) V Bool (D × Bool) A B where
  edge := G.incidenceEdge
  project := π

@[simp] lemma incidence_source_false (π : (V × D) × Bool → A → B) (v : V) (d : D) :
    (G.incidence π).source v (d,false)=((v,d),false) := rfl
@[simp] lemma incidence_source_true (π : (V × D) × Bool → A → B) (v : V) (d : D) :
    (G.incidence π).source v (d,true)=(G.rotate (v,d),true) := rfl

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
noncomputable def down (h : V × D → ℝ) (v : V) : ℝ :=
  𝔼 d, (h (v,d)+h (G.rotate (v,d)))/2
noncomputable def up (h : V → ℝ) (p : V × D) : ℝ :=
  (h p.1+h (G.rotate p).1)/2

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma incidence_average (π : (V × D) × Bool → A → B) (h : V × D → ℝ) :
    (G.incidence π).average h=G.down h := by
  funext v
  unfold BiProjection.average down
  rw [expect_prod]
  apply expect_congr rfl
  intro d _
  rw [expect_bool]
  rfl

omit [Nonempty V] [Nonempty D] in
lemma down_mean (h : V × D → ℝ) : (𝔼 v, G.down h v)=𝔼 p, h p := by
  have he := (G.incidence (fun (_ : (V × D) × Bool) (_ : Unit) => ())).average_mean h
  rwa [G.incidence_average] at he

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma down_sub (h k : V × D → ℝ) : G.down (fun p => h p-k p)=fun v => G.down h v-G.down k v := by
  funext v
  unfold down
  rw [← expect_sub_distrib]
  apply expect_congr rfl
  intro d _
  ring
omit [Fintype V] [Nonempty V] in
lemma down_const (c : ℝ) : G.down (fun _ => c)=fun _ => c := by
  funext v
  simp only [down,show (c+c)/2=c by ring,Fintype.expect_const]

omit [Nonempty V] [Nonempty D] in
lemma down_up_adjoint (f : V × D → ℝ) (g : V → ℝ) :
    pairing (G.down f) g=pairing f (G.up g) := by
  have hr := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.rotate p)*g p.1)
    (fun p : V × D => f p*g (G.rotate p).1)
    (by intro p; rw [G.involutive])
  unfold pairing down up
  simp only [expect_mul]
  rw [← expect_prod (fun p : V × D => ((f p+f (G.rotate p))/2)*g p.1)]
  have he (p : V × D) : ((f p+f (G.rotate p))/2)*g p.1=
      (f p*g p.1+f (G.rotate p)*g p.1)/2 := by ring
  have hf (p : V × D) : f p*((g p.1+g (G.rotate p).1)/2)=
      (f p*g p.1+f p*g (G.rotate p).1)/2 := by ring
  simp_rw [he,hf]
  rw [← expect_div,← expect_div,expect_add_distrib,expect_add_distrib,hr]

omit [Nonempty V] in
lemma up_energy (g : V → ℝ) :
    energy (G.up g)=(energy g+pairing g (G.adjacency g))/2 := by
  have hr : (𝔼 p : V × D, g (G.rotate p).1^2)=energy g := by
    rw [Fintype.expect_equiv G.rotate _ (fun p : V × D => g p.1^2) (fun _ => rfl),expect_prod]
    simp only [Fintype.expect_const,energy]
  have he (p : V × D) : ((g p.1+g (G.rotate p).1)/2)^2=
      (g p.1^2+g (G.rotate p).1^2+2*(g p.1*g (G.rotate p).1))/4 := by ring
  change (𝔼 p : V × D, ((g p.1+g (G.rotate p).1)/2)^2)=_
  simp_rw [he]
  rw [← expect_div,expect_add_distrib,expect_add_distrib,← mul_expect,hr]
  have hf : (𝔼 p : V × D, g p.1^2)=energy g := by
    rw [expect_prod]; simp only [Fintype.expect_const,energy]
  rw [hf]
  have hg : (𝔼 p : V × D, g p.1*g (G.rotate p).1)=pairing g (G.adjacency g) := by
    unfold pairing adjacency
    rw [expect_prod]
    simp_rw [mul_expect]
    rfl
  rw [hg]
  ring
end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceOperator

end OAI
