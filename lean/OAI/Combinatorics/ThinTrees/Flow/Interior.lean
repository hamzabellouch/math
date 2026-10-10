import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Grid
import OAI.Combinatorics.ThinTrees.Flow.FractionalPackingMargin

namespace OAI

/-! Flow interior. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

namespace FlowPoint

def bump (F : FlowPoint n m) (γ : ℝ) : FlowPoint n m :=
  ⟨fun e => F.x e+γ,fun r e => F.a r e+γ,fun r e => F.b r e+γ⟩

def Close (F H : FlowPoint n m) (ρ : ℝ) : Prop :=
  (∀e, |F.x e-H.x e| ≤ ρ) ∧
  (∀r e, |F.a r e-H.a r e| ≤ ρ) ∧ (∀r e, |F.b r e-H.b r e| ≤ ρ)

def Bounded (F : FlowPoint n m) (R : ℝ) : Prop :=
  (∀e, |F.x e| ≤ R) ∧ (∀r e, |F.a r e| ≤ R) ∧ (∀r e, |F.b r e| ≤ R)

lemma Exact.bump_bound {G : MultiGraph n m} {c : Fin m → ℝ} {q R γ : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) (hc : ∀e, c e ≤ R) (hγ : 0 ≤ γ) :
    (F.bump γ).Bounded (R+γ) := by
  refine ⟨?_,?_,?_⟩
  · intro e
    change |F.x e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.1 e).1 hγ)]
    linarith only [(hF.1 e).2, hc e]
  · intro r e
    change |F.a r e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.2.1 r e).1 hγ)]
    have h := (hF.2.1 r e).2.2
    linarith only [h,(hF.2.1 r e).2.1,(hF.1 e).2,hc e]
  · intro r e
    change |F.b r e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.2.1 r e).2.1 hγ)]
    have h := (hF.2.1 r e).2.2
    linarith only [h,(hF.2.1 r e).1,(hF.1 e).2,hc e]

end FlowPoint

lemma out_perturb_upper (G : MultiGraph n m) {a b a' b' : Fin m → ℝ} {σ : ℝ}
    (hσ : 0 ≤ σ) (ha : ∀e, a' e ≤ a e+σ) (hb : ∀e, b' e ≤ b e+σ) (v : Fin n) :
    out G a' b' v ≤ out G a b v+2*m*σ := by
  have hi (e : Fin m) :
      (if G.left e=v then a' e else 0)+(if G.right e=v then b' e else 0) ≤
        (if G.left e=v then a e else 0)+(if G.right e=v then b e else 0)+2*σ := by
    split_ifs <;> linarith only [ha e,hb e,hσ]
  have h := sum_le_sum (s:=univ) fun e _ => hi e
  simpa only [out,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_comm (m:ℝ),mul_assoc] using h

lemma exact_bump_cube (G : MultiGraph n m) {c : Fin m → ℝ} {qbar ε α γ : ℝ}
    (hγ : 0 < γ) (hα : 0 ≤ α) (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε)
    (hmγ : 4*m*γ ≤ α) {F : FlowPoint n m}
    (hF : F.Exact G (fun e => c e-2*γ) (qbar-α)) {H : FlowPoint n m}
    (hclose : H.Close (F.bump γ) (γ/4)) : H.Feasible G c qbar ε := by
  have hx (e : Fin m) := abs_le.mp (hclose.1 e)
  have ha (r : Fin n) (e : Fin m) := abs_le.mp (hclose.2.1 r e)
  have hb (r : Fin n) (e : Fin m) := abs_le.mp (hclose.2.2 r e)
  simp only [FlowPoint.bump] at hx ha hb
  have hg : 0 ≤ (m:ℝ)*γ := mul_nonneg (Nat.cast_nonneg _) hγ.le
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    constructor
    · linarith only [(hx e).1,(hF.1 e).1,hγ]
    · linarith only [(hx e).2,(hF.1 e).2,hγ]
  · intro r e
    refine ⟨?_,?_,?_⟩
    · linarith only [(ha r e).1,(hF.2.1 r e).1,hγ]
    · linarith only [(hb r e).1,(hF.2.1 r e).2.1,hγ]
    · linarith only [(hx e).2,(ha r e).1,(hb r e).1,(hF.2.1 r e).2.2,hγ]
  · intro r v
    have ho := out_perturb_upper G (show 0 ≤ γ+γ/4 by linarith)
      (fun e => show H.a r e ≤ F.a r e+(γ+γ/4) by linarith only [(ha r e).2])
      (fun e => show H.b r e ≤ F.b r e+(γ+γ/4) by linarith only [(hb r e).2]) v
    rw [hF.2.2.1] at ho
    split_ifs at ho ⊢ <;> nlinarith only [ho,hmγ,hα,hαε,hg]
  · have hsum : (∑e, F.x e) ≤ ∑e, H.x e := sum_le_sum fun e _ => by
      linarith only [(hx e).1,hγ]
    rw [hF.2.2.2] at hsum
    nlinarith only [hsum,hαn]

lemma capacity_shift_lower (G : MultiGraph n m) (c : Fin m → ℝ) {γ : ℝ}
    (hγ : 0 ≤ γ) (p : Setoid (Fin n)) :
    capacity G.left G.right c p-γ*m ≤ capacity G.left G.right (fun e => c e-γ) p := by
  rw [capacity_eq_sum,capacity_eq_sum]
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul]
  have hc : (Partitions.crossing G p).card ≤ m :=
    (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin m))
  have hc' : ((Partitions.crossing G p).card:ℝ) ≤ m := by exact_mod_cast hc
  nlinarith only [mul_le_mul_of_nonneg_left hc' hγ]

theorem flow_inner_cube (G : MultiGraph n m) (hn : 0 < n) (c : Fin m → ℝ)
    {qbar ε α β γ R : ℝ} (hγ : 0 < γ) (hα : 0 ≤ α) (hq : α ≤ qbar)
    (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε) (hβ : 0 < β)
    (hmγα : 4*m*γ ≤ α) (hmγβ : 4*m*γ ≤ β)
    (hc : ∀e, 2*γ ≤ c e) (hcR : ∀e, c e ≤ R)
    (hp : ∀p : Setoid (Fin n), (qbar+β)*((partCount p:ℝ)-1) ≤ capacity G.left G.right c p) :
    ∃F : FlowPoint n m, F.Bounded (R+γ) ∧
      ∀H : FlowPoint n m, H.Close F (γ/4) → H.Feasible G c qbar ε := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hmargin (p : Setoid (Fin n)) :
      (qbar-α+β/2)*((partCount p:ℝ)-1) ≤ capacity G.left G.right (fun e => c e-2*γ) p := by
    by_cases htop : p=⊤
    · subst p
      simp [capacity,crossingIndicator,partCount_top]
    · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
      have ha : 0 ≤ α*((partCount p:ℝ)-1) := mul_nonneg hα (by linarith)
      have hb : β ≤ β*((partCount p:ℝ)-1) := by nlinarith only [hd,hβ]
      have hs := capacity_shift_lower G c (show 0 ≤ 2*γ by linarith only [hγ]) p
      nlinarith only [hs,hp p,ha,hb,hmγβ]
  obtain ⟨F,hF⟩ := exact_flow_of_margin G hn (fun e => c e-2*γ)
    (fun e => sub_nonneg.mpr (hc e)) (sub_nonneg.mpr hq) (show 0 < β/2 by linarith) hmargin
  refine ⟨F.bump γ,hF.bump_bound (fun e => ?_) hγ.le,fun H hH => ?_⟩
  · linarith only [hcR e,hγ]
  · exact exact_bump_cube G hγ hα hαε hαn hmγα hF hH

end
end AlgorithmicThinTrees.Orientations

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma exact_bump_cube_vary (G : MultiGraph n m) {c c' : Fin m → ℝ} {qbar ε α γ : ℝ}
    (hγ : 0 < γ) (hα : 0 ≤ α) (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε)
    (hmγ : 4*m*γ ≤ α) {F : FlowPoint n m}
    (hF : F.Exact G (fun e => c e-2*γ) (qbar-α))
    (hc' : ∀e, c e-γ/2 ≤ c' e) {H : FlowPoint n m}
    (hclose : H.Close (F.bump γ) (γ/4)) : H.Feasible G c' qbar ε := by
  have h := exact_bump_cube G hγ hα hαε hαn hmγ hF hclose
  refine ⟨?_,h.2⟩
  intro e
  refine ⟨(h.1 e).1,?_⟩
  have hx := (abs_le.mp (hclose.1 e)).2
  change H.x e-(F.x e+γ) ≤ γ/4 at hx
  linarith only [hx,(hF.1 e).2,hc' e,hγ]

theorem flow_inner_cube_vary (G : MultiGraph n m) (hn : 0 < n) (c : Fin m → ℝ)
    {qbar ε α β γ R : ℝ} (hγ : 0 < γ) (hα : 0 ≤ α) (hq : α ≤ qbar)
    (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε) (hβ : 0 < β)
    (hmγα : 4*m*γ ≤ α) (hmγβ : 4*m*γ ≤ β)
    (hc : ∀e, 2*γ ≤ c e) (hcR : ∀e, c e ≤ R)
    (hp : ∀p : Setoid (Fin n), (qbar+β)*((partCount p:ℝ)-1) ≤ capacity G.left G.right c p) :
    ∃F : FlowPoint n m, F.Bounded (R+γ) ∧
      ∀(c' : Fin m → ℝ) (H : FlowPoint n m),
        (∀e, c e-γ/2 ≤ c' e) → H.Close F (γ/4) → H.Feasible G c' qbar ε := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hmargin (p : Setoid (Fin n)) :
      (qbar-α+β/2)*((partCount p:ℝ)-1) ≤ capacity G.left G.right (fun e => c e-2*γ) p := by
    by_cases htop : p=⊤
    · subst p
      simp [capacity,crossingIndicator,partCount_top]
    · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
      have ha : 0 ≤ α*((partCount p:ℝ)-1) := mul_nonneg hα (by linarith)
      have hb : β ≤ β*((partCount p:ℝ)-1) := by nlinarith only [hd,hβ]
      have hs := capacity_shift_lower G c (show 0 ≤ 2*γ by linarith only [hγ]) p
      nlinarith only [hs,hp p,ha,hb,hmγβ]
  obtain ⟨F,hF⟩ := exact_flow_of_margin G hn (fun e => c e-2*γ)
    (fun e => sub_nonneg.mpr (hc e)) (sub_nonneg.mpr hq) (show 0 < β/2 by linarith) hmargin
  refine ⟨F.bump γ,hF.bump_bound (fun e => ?_) hγ.le,?_⟩
  · linarith only [hcR e,hγ]
  · intro c' H hc' hH
    exact exact_bump_cube_vary G hγ hα hαε hαn hmγα hF hc' hH

lemma FlowPoint.Close.mono {F H : FlowPoint n m} {ρ σ : ℝ}
    (h : F.Close H ρ) (hρσ : ρ ≤ σ) : F.Close H σ :=
  ⟨fun e => (h.1 e).trans hρσ,fun r e => (h.2.1 r e).trans hρσ,
    fun r e => (h.2.2 r e).trans hρσ⟩

lemma FlowPoint.Bounded.mono {F : FlowPoint n m} {R R' : ℝ}
    (h : F.Bounded R) (hRR' : R ≤ R') : F.Bounded R' :=
  ⟨fun e => (h.1 e).trans hRR',fun r e => (h.2.1 r e).trans hRR',
    fun r e => (h.2.2 r e).trans hRR'⟩
end
end AlgorithmicThinTrees.Orientations
end

end OAI
