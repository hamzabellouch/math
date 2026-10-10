import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

abbrev Vertex := ℤ × ℤ

def square (N : ℕ) : Finset Vertex :=
  (Finset.Icc 0 (N:ℤ)) ×ˢ (Finset.Icc 0 (N:ℤ))

def dist₁ (x y : Vertex) : ℝ :=
  |(x.1:ℝ)-y.1|+|(x.2:ℝ)-y.2|

def ball (N : ℕ) (x : Vertex) (r : ℝ) : Finset Vertex :=
  (square N).filter (fun y => dist₁ x y ≤ r)

def mean (N : ℕ) (v : Vertex → ℝ) : ℝ :=
  (∑ x ∈ square N, v x) / (square N).card

def energy (N : ℕ) (p : ℝ) (v : Vertex → ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc (0:ℤ) ((N:ℤ)-1), ∑ j ∈ Finset.Icc (0:ℤ) N,
    |v (i+1,j)-v (i,j)|^p) +
  (∑ i ∈ Finset.Icc (0:ℤ) N, ∑ j ∈ Finset.Icc (0:ℤ) ((N:ℤ)-1),
    |v (i,j+1)-v (i,j)|^p)

def embedNat (x : NatGrid.Vertex) : Vertex := ((x.1:ℤ),(x.2:ℤ))

lemma embedNat_injective : Function.Injective embedNat := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [embedNat] at h1 h2
  apply Prod.ext
  · exact_mod_cast h1
  · exact_mod_cast h2

lemma square_map (N : ℕ) :
    (NatGrid.square N).map ⟨embedNat,embedNat_injective⟩ = square N := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨y,hy,rfl⟩
    change embedNat y ∈ square N
    have hy := NatGrid.square_mem.mp hy
    simp only [square,Finset.mem_product,Finset.mem_Icc,embedNat]
    exact ⟨⟨by positivity,by exact_mod_cast hy.1⟩,⟨by positivity,by exact_mod_cast hy.2⟩⟩
  · intro hx
    have hx := Finset.mem_product.mp hx
    have hx1 := Finset.mem_Icc.mp hx.1
    have hx2 := Finset.mem_Icc.mp hx.2
    refine ⟨(x.1.toNat,x.2.toNat),NatGrid.square_mem.mpr ⟨by omega,by omega⟩,?_⟩
    simp [embedNat,Int.toNat_of_nonneg hx1.1,Int.toNat_of_nonneg hx2.1]

lemma sum_square (N : ℕ) (f : Vertex → ℝ) :
    (∑ x ∈ NatGrid.square N, f (embedNat x)) = ∑ x ∈ square N, f x := by
  rw [← square_map,Finset.sum_map]
  rfl

lemma embed_dist (x y : NatGrid.Vertex) : dist₁ (embedNat x) (embedNat y) = NatGrid.dist₁ x y := by
  simp [dist₁,NatGrid.dist₁,embedNat]

lemma ball_map (N : ℕ) (x : NatGrid.Vertex) (r : ℝ) :
    (NatGrid.ball N x r).map ⟨embedNat,embedNat_injective⟩ = ball N (embedNat x) r := by
  rw [ball,← square_map,Finset.filter_map]
  change (NatGrid.ball N x r).map _ =
    ((NatGrid.square N).filter (fun y => dist₁ (embedNat x) (embedNat y) ≤ r)).map _
  simp only [NatGrid.ball,embed_dist]

lemma sum_ball (N : ℕ) (x : NatGrid.Vertex) (r : ℝ) (f : Vertex → ℝ) :
    (∑ y ∈ NatGrid.ball N x r, f (embedNat y)) = ∑ y ∈ ball N (embedNat x) r, f y := by
  rw [← ball_map,Finset.sum_map]
  rfl

lemma embed_mem_square {N : ℕ} {x : NatGrid.Vertex} (hx : x ∈ NatGrid.square N) :
    embedNat x ∈ square N := by
  rw [← square_map]
  exact Finset.mem_map.mpr ⟨x,hx,rfl⟩

lemma avg_embed (N : ℕ) (v : Vertex → ℝ) :
    NatGrid.avg (NatGrid.square N) (v ∘ embedNat) = mean N v := by
  rw [NatGrid.avg,mean]
  rw [show (∑ x ∈ NatGrid.square N, (v ∘ embedNat) x) = ∑ x ∈ square N, v x from sum_square N v]
  rw [← square_map,Finset.card_map]

lemma sum_nat_Icc (N : ℕ) (f : ℤ → ℝ) :
    (∑ i ∈ Finset.Icc 0 N, f (i:ℤ)) = ∑ i ∈ Finset.Icc (0:ℤ) N, f i := by
  apply Finset.sum_bij (fun (i : ℕ) _ => (i:ℤ))
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨by positivity,by exact_mod_cast hi.2⟩
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro i hi
    have hi := Finset.mem_Icc.mp hi
    exact ⟨i.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros;rfl

lemma sum_nat_Ico (N : ℕ) (f : ℤ → ℝ) :
    (∑ i ∈ Finset.Ico 0 N, f (i:ℤ)) = ∑ i ∈ Finset.Icc (0:ℤ) ((N:ℤ)-1), f i := by
  apply Finset.sum_bij (fun (i : ℕ) _ => (i:ℤ))
  · intro i hi
    simp only [Finset.mem_Ico,Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro i hi
    have hi := Finset.mem_Icc.mp hi
    exact ⟨i.toNat,Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros;rfl

lemma energy_embed (N : ℕ) (p : ℝ) (v : Vertex → ℝ) :
    NatGrid.energy N p (v ∘ embedNat) = energy N p v := by
  simp only [NatGrid.energy,NatGrid.edges,Finset.sum_disjSum,Finset.sum_product]
  simp only [NatGrid.edgeGrad,Function.comp_apply,embedNat,Nat.cast_add,Nat.cast_one]
  unfold energy
  congr 1
  · have hj (i : ℤ) := sum_nat_Icc N (fun j => |v (i+1,j)-v (i,j)|^p)
    simp_rw [hj]
    exact sum_nat_Ico N (fun i => ∑ j ∈ Finset.Icc (0:ℤ) N, |v (i+1,j)-v (i,j)|^p)
  · have hj (i : ℤ) := sum_nat_Ico N (fun j => |v (i,j+1)-v (i,j)|^p)
    simp_rw [hj]
    exact sum_nat_Icc N (fun i => ∑ j ∈ Finset.Icc (0:ℤ) ((N:ℤ)-1), |v (i,j+1)-v (i,j)|^p)

theorem spread_trace (p α C : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hα : 2-p < α) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (ν v : Vertex → ℝ),
      (∀ x ∈ square N, 0 ≤ ν x) → (∑ x ∈ square N, ν x) ≤ C →
      (∀ x ∈ square N, ∀ r : ℝ, 0 ≤ r → r ≤ 2*(N:ℝ) →
        (∑ y ∈ ball N x r, ν y) ≤ C*((r+1)/(N:ℝ))^α) →
      |(∑ x ∈ square N, ν x*v x) - (∑ x ∈ square N, ν x)*mean N v| ≤
        K*(N:ℝ)^(1-2/p)*(energy N p v)^(1/p) := by
  obtain ⟨K,hK,h⟩ := NatGrid.spread_trace p α C hp hp2 hα hC
  refine ⟨K,hK,?_⟩
  intro N hN ν v hν hmass hspread
  have hid := h N hN (ν ∘ embedNat) (v ∘ embedNat)
    (fun x hx => hν _ (embed_mem_square hx))
    (by simpa only [Function.comp_apply,sum_square] using hmass)
    (by
      intro x hx r hr hrN
      rw [show (∑ y ∈ NatGrid.ball N x r, (ν ∘ embedNat) y) =
        ∑ y ∈ ball N (embedNat x) r, ν y from sum_ball N x r ν]
      exact hspread _ (embed_mem_square hx) r hr hrN)
  rw [avg_embed,energy_embed] at hid
  have hνsum := sum_square N ν
  have hνvsum := sum_square N (fun x => ν x*v x)
  simpa only [Function.comp_apply,hνsum,hνvsum] using hid

end GridTrace

end

end OAI
