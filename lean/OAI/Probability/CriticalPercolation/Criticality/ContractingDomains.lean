import Mathlib
import OAI.Probability.CriticalPercolation.Modular.GraphModular
import OAI.Probability.CriticalPercolation.Modular.ModularCharacter
import OAI.Probability.CriticalPercolation.Modular.ModularGrowth
import OAI.Probability.CriticalPercolation.Criticality.MinimalPair

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_aut_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio (φ.vertex x) o =
      G.modularRatio (φ.vertex o) o * G.modularRatio x o := by
  rw [←G.modularRatio_cocycle hc hl (φ.vertex x) (φ.vertex o) o,
    Aut.modularRatio,mul_comm]

lemma exists_weight_contraction (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ φ : G.Aut, G.modularRatio (φ.vertex o) o < 1 := by
  by_contra hn
  apply hu
  intro φ x
  have hlow : ∀ ψ : G.Aut, 1 ≤ G.modularRatio (ψ.vertex o) o := by
    intro ψ
    exact le_of_not_gt (fun h => hn ⟨ψ,h⟩)
  have h1 := hlow φ
  have h2 := hlow φ⁻¹
  have hprod : G.modularRatio (φ.vertex o) o *
      G.modularRatio ((φ⁻¹).vertex o) o = 1 := by
    have h := G.modularRatio_aut_weight hc hl o ((φ⁻¹).vertex o) φ
    have he : φ.vertex ((φ⁻¹).vertex o)=o := φ.vertex.apply_symm_apply o
    rw [he,G.modularRatio_self] at h
    exact h.symm
  have he1 : G.modularRatio (φ.vertex o) o=1 := by nlinarith
  have he2 : G.modularRatio o (φ.vertex o)=1 := by
    have h := G.modularRatio_cocycle hc hl o (φ.vertex o) o
    rw [he1,mul_one,G.modularRatio_self] at h
    exact h
  have he := G.modularRatio_aut_base hc hl o x φ
  rw [he2] at he
  unfold modularRatio at he
  have hz : (G.suborbitCard (φ.vertex x) x : ℝ)≠0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl _ _))
  exact_mod_cast (div_eq_one_iff_eq hz).mp he

lemma uniform_weight_contraction (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ c : ℝ, 0<c ∧ c<1 ∧ ∃ R : ℕ, ∀ z : V, ∃ ψ : G.Aut,
      ψ.vertex z ∈ G.vertexBall z R ∧
      ∀ y, G.modularRatio (ψ.vertex y) o=c*G.modularRatio y o := by
  obtain ⟨φ,hφ⟩ := G.exists_weight_contraction hc hl hu o
  let c := G.modularRatio (φ.vertex o) o
  obtain ⟨S,hS,hcover⟩ := hq
  have hpath : ∀ z : S, ∃ n, φ.vertex z.val ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hc _ _)
  choose n hn using hpath
  let := hS.fintype
  let R := ∑ z : S, n z
  refine ⟨c,G.modularRatio_pos hc hl _ _,hφ,R,?_⟩
  intro z
  obtain ⟨s,hs,τ,rfl⟩ := hcover z
  refine ⟨τ*φ*τ⁻¹,?_,?_⟩
  · change τ.vertex (φ.vertex (τ.vertex.symm (τ.vertex s))) ∈ _
    rw [Equiv.symm_apply_apply,Aut.vertexBall_mem]
    exact G.vertexBall_mono s (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨s,hs⟩ : S))) (hn ⟨s,hs⟩)
  · intro y
    change G.modularRatio (τ.vertex (φ.vertex (τ.vertex.symm y))) o = _
    rw [G.modularRatio_aut_weight hc hl o _ τ,
      G.modularRatio_aut_weight hc hl o _ φ]
    have ht := G.modularRatio_aut_weight hc hl o (τ.vertex.symm y) τ
    rw [Equiv.apply_symm_apply] at ht
    change _ = c * G.modularRatio y o
    rw [ht]
    ring

def safeBallDomain (o : V) (T : ℝ) (R : ℕ) : Set V :=
  {x | ∃ z, x∈G.vertexBall z R ∧
    ∀ y∈G.vertexBall z R, G.modularRatio y o≤T}

lemma safeBallDomain_mono (o : V) (R : ℕ) : Monotone (fun T => G.safeBallDomain o T R) := by
  rintro A B h x ⟨z,hx,hz⟩
  exact ⟨z,hx,fun y hy => (hz y hy).trans h⟩

lemma safeBallDomain_subset (o : V) (T : ℝ) (R : ℕ) :
    G.safeBallDomain o T R⊆{x | G.modularRatio x o≤T} := by
  rintro x ⟨z,hx,hz⟩
  exact hz x hx

lemma modularRatio_ball_upper (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ z y, y∈G.vertexBall z R → G.modularRatio y z≤C := by
  obtain ⟨M,hM,hbound⟩ := G.uniform_positive_ball_bound hq R
  refine ⟨M,by exact_mod_cast hM,?_⟩
  intro z y hy
  calc
    G.modularRatio y z ≤ (G.suborbitCard y z : ℝ) := G.modularRatio_le_suborbitCard hc hl y z
    _ ≤ M := by
      exact_mod_cast (Set.ncard_le_ncard
        (G.stabilizerOrbit_subset_ball ((G.vertexBall_comm).mp hy))
        (G.vertexBall_finite hl y R)).trans (hbound y)

lemma safeBallDomain_low_inclusion (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ o T, {x | G.modularRatio x o≤T/C}⊆G.safeBallDomain o T R := by
  obtain ⟨C,hC,hbound⟩ := G.modularRatio_ball_upper hc hl hq R
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C,hC,?_⟩
  rintro o T x hx
  refine ⟨x,G.mem_vertexBall_self x R,?_⟩
  intro y hy
  rw [←G.modularRatio_cocycle hc hl y x o]
  calc
    G.modularRatio y x * G.modularRatio x o ≤ C*G.modularRatio x o :=
      mul_le_mul_of_nonneg_right (hbound x y hy) (G.modularRatio_pos hc hl x o).le
    _ ≤ T := by
      have hh := (le_div_iff₀ hCp).mp hx
      simpa only [mul_comm] using hh

def InsideWalk (S : Set V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.fullGraph.Walk x y, p.length≤n ∧ ∀ v∈p.support, v∈S

lemma InsideWalk.mono {S D : Set V} {x y : V} {n m : ℕ}
    (h : G.InsideWalk S x y n) (hSD : S ⊆ D) (hnm : n ≤ m) :
    G.InsideWalk D x y m := by
  obtain ⟨p,hp,hs⟩ := h
  exact ⟨p,hp.trans hnm,fun v hv => hSD (hs v hv)⟩

lemma InsideWalk.refl {S : Set V} {x : V} (hx : x∈S) :
    G.InsideWalk S x x 0 := by
  refine ⟨.nil,le_rfl,?_⟩
  intro v hv
  have he : v=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
  exact he.symm ▸ hx

lemma InsideWalk.reverse {S : Set V} {x y : V} {n : ℕ}
    (h : G.InsideWalk S x y n) : G.InsideWalk S y x n := by
  obtain ⟨p,hp,hs⟩ := h
  refine ⟨p.reverse,by simpa only [SimpleGraph.Walk.length_reverse] using hp,?_⟩
  intro v hv
  exact hs v (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)

lemma InsideWalk.append {S : Set V} {x y z : V} {n m : ℕ}
    (h : G.InsideWalk S x y n) (h' : G.InsideWalk S y z m) :
    G.InsideWalk S x z (n+m) := by
  obtain ⟨p,hp,hs⟩ := h
  obtain ⟨q,hq,ht⟩ := h'
  refine ⟨p.append q,by simpa only [SimpleGraph.Walk.length_append] using Nat.add_le_add hp hq,?_⟩
  intro v hv
  exact ((SimpleGraph.Walk.mem_support_append_iff p q).mp hv).elim (hs v) (ht v)

lemma insideWalk_ball {z x : V} {R : ℕ} (hx : x∈G.vertexBall z R) :
    G.InsideWalk (G.vertexBall z R) z x R := by
  obtain ⟨p,hp⟩ := G.mem_vertexBall_iff_walk.mp hx
  refine ⟨p,hp,?_⟩
  intro v hv
  exact G.vertexBall_mono z ((p.length_takeUntil_le_length hv).trans hp)
    (G.walk_mem_vertexBall (p.takeUntil v hv))

lemma modularRatio_weight_pow (o : V) (φ : G.Aut) (c : ℝ)
    (hφ : ∀ y, G.modularRatio (φ.vertex y) o=c*G.modularRatio y o)
    (n : ℕ) (y : V) :
    G.modularRatio ((φ^n).vertex y) o=c^n*G.modularRatio y o := by
  induction n with
  | zero => simp only [pow_zero,one_mul]; rfl
  | succ n ih =>
    rw [pow_succ']
    change G.modularRatio (φ.vertex ((φ^n).vertex y)) o = _
    rw [hφ,ih,pow_succ']
    ring

lemma safeBallDomain_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (T : ℝ) (R : ℕ) (z : V) (c : ℝ) (hc0 : 0<c) (hc1 : c≤1)
    (φ : G.Aut) (hstep : φ.vertex z∈G.vertexBall z R)
    (hφ : ∀ y, G.modularRatio (φ.vertex y) o=c*G.modularRatio y o)
    (hball : ∀ y∈G.vertexBall z R, G.modularRatio y o≤T) (n : ℕ) :
    G.InsideWalk (G.safeBallDomain o T R) z ((φ^n).vertex z) (n*R) ∧
      G.modularRatio ((φ^n).vertex z) o≤c^n*T := by
  have hT : 0≤T := (G.modularRatio_pos hc hl z o).le.trans
    (hball z (G.mem_vertexBall_self z R))
  have hballs (m : ℕ) : G.vertexBall ((φ^m).vertex z) R⊆G.safeBallDomain o T R := by
    intro x hx
    refine ⟨(φ^m).vertex z,hx,?_⟩
    intro y hy
    obtain ⟨a,rfl⟩ := (φ^m).vertex.surjective y
    have ha := (Aut.vertexBall_mem G (φ^m) z a R).mp hy
    rw [G.modularRatio_weight_pow o φ c hφ]
    calc
      c^m*G.modularRatio a o ≤ c^m*T :=
        mul_le_mul_of_nonneg_left (hball a ha) (pow_nonneg hc0.le m)
      _ ≤ T := mul_le_of_le_one_left hT (pow_le_one₀ hc0.le hc1)
  constructor
  · induction n with
    | zero =>
      rw [pow_zero,Nat.zero_mul]
      change G.InsideWalk (G.safeBallDomain o T R) z z 0
      exact InsideWalk.refl G (hballs 0 (G.mem_vertexBall_self z R))
    | succ n ih =>
      have hs : (φ^(n+1)).vertex z∈G.vertexBall ((φ^n).vertex z) R := by
        rw [pow_succ]
        exact (Aut.vertexBall_mem G (φ^n) z (φ.vertex z) R).mpr hstep
      have hw := (G.insideWalk_ball hs).mono G (hballs n) le_rfl
      have hh := ih.append G hw
      simpa only [Nat.add_mul,Nat.one_mul] using hh
  · rw [G.modularRatio_weight_pow o φ c hφ]
    exact mul_le_mul_of_nonneg_left (hball z (G.mem_vertexBall_self z R)) (pow_nonneg hc0.le n)

theorem safeBallDomain_uniform_descent (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ R : ℕ, ∃ C : ℝ, 1≤C ∧
      (∀ T, {x | G.modularRatio x o≤T/C}⊆G.safeBallDomain o T R) ∧
      ∀ a : ℝ, 0<a → ∃ L : ℕ, ∀ T : ℝ, ∀ x∈G.safeBallDomain o T R,
        ∃ y, G.modularRatio y o≤a*T ∧ G.InsideWalk (G.safeBallDomain o T R) x y L := by
  obtain ⟨c,hc0,hc1,R,hcon⟩ := G.uniform_weight_contraction hc hl hq hu o
  obtain ⟨C,hC,hClow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  refine ⟨R,C,hC,hClow o,?_⟩
  intro a ha
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one ha hc1
  refine ⟨R+n*R,?_⟩
  rintro T x ⟨z,hx,hball⟩
  obtain ⟨φ,hstep,hφ⟩ := hcon z
  have hi := G.safeBallDomain_iterate hc hl o T R z c hc0 hc1.le φ hstep hφ hball n
  refine ⟨(φ^n).vertex z,?_,?_⟩
  · have hT : 0≤T := (G.modularRatio_pos hc hl z o).le.trans
      (hball z (G.mem_vertexBall_self z R))
    exact hi.2.trans (mul_le_mul_of_nonneg_right hn.le hT)
  · have hw := (G.insideWalk_ball hx).reverse G
    have hd : G.vertexBall z R⊆G.safeBallDomain o T R := fun y hy => ⟨z,hy,hball⟩
    exact (hw.mono G hd le_rfl).append G hi.1

end CriticalPercolation.BondGraph
end
end

end OAI
