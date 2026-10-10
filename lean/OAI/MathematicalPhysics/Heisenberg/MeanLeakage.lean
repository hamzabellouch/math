import OAI.MathematicalPhysics.Heisenberg.WeightedLeakage

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace Heisenberg.FiniteLeakage

section
open scoped RealInnerProductSpace
variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype Ω]

lemma triangle_prefix_le_one {n : ℕ} (hn : 0<n) (i : Fin n) :
    (∑ j : Fin n,if j ≤ i then triangle j else 0) ≤ 1 := by
  rw [←triangle_sum hn]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact triangle_nonneg j

theorem expected_chain_leakage (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1)
    (C : Ω → ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hC : ∀ ω j,j<n → ∀ v,‖C ω j v‖ ≤ ‖v‖)
    (eta : H) (g : Ω → H) (horth : ∀ ω,⟪eta,g ω⟫=0)
    (energy pair err residual : Ω → Fin n → ℝ) (A δ E B : ℝ)
    (hA : 0≤A) (hδ : 0<δ) (hB : 0≤B)
    (henergy : ∀ ω i,0≤energy ω i)
    (hpair : ∀ ω i,(pair ω i)^2 ≤ A*energy ω i)
    (happrox : ∀ ω (i : Fin n),⟪chain (C ω) i eta,chain (C ω) i (eta+g ω)⟫ ≤ err ω i+pair ω i)
    (henergy_loss : ∀ ω i,2*δ*energy ω i ≤
      ‖chain (C ω) i (eta+g ω)‖^2-‖chain (C ω) (i+1) (eta+g ω)‖^2+residual ω i)
    (herr : ∀ i,∑ ω,μ ω*err ω i ≤ E)
    (hres : ∀ i,∑ ω,μ ω*residual ω i ≤ B) :
    ‖eta‖^2-2*E-2*A/(δ*(n:ℝ))-(n:ℝ)*B ≤
      ∑ ω,μ ω*(‖eta+g ω‖^2-‖chain (C ω) n (eta+g ω)‖^2) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (contraction_chain_leakage (C ω) n hn (hC ω) eta (g ω)
      (horth ω) (energy ω) (pair ω) (err ω) (residual ω) A δ hA hδ
      (henergy ω) (hpair ω) (happrox ω) (henergy_loss ω)) (hμ ω))
  let W : Fin n → ℝ := fun i => ∑ j,if j ≤ i then triangle j else 0
  have swap (f : Ω → Fin n → ℝ) (w : Fin n → ℝ) :
      (∑ ω,μ ω*(∑ i,w i*f ω i))=∑ i,w i*(∑ ω,μ ω*f ω i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have he : (∑ ω,μ ω*(∑ i,triangle i*err ω i)) ≤ E := by
    rw [swap]
    calc
      _ ≤ ∑ i,triangle i*E := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (herr i) (triangle_nonneg i))
      _ = E := by rw [←Finset.sum_mul,triangle_sum hn,one_mul]
  have hr : (∑ ω,μ ω*(∑ i,W i*residual ω i)) ≤ (n:ℝ)*B := by
    rw [swap]
    calc
      _ ≤ ∑ i,W i*B := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hres i) (triangle_prefix_pos i).le)
      _ ≤ ∑ _i : Fin n,B := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left hB (triangle_prefix_le_one hn i))
      _ = _ := by simp
  have heq : (∑ ω, μ ω *
      (‖eta‖^2-2*(∑ i,triangle i*err ω i)-2*A/(δ*(n:ℝ))-(∑ i,W i*residual ω i))) =
      ‖eta‖^2-2*(∑ ω,μ ω*(∑ i,triangle i*err ω i))-2*A/(δ*(n:ℝ))-
        (∑ ω,μ ω*(∑ i,W i*residual ω i)) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul]
    simp only [mul_left_comm (μ _) (2:ℝ),←Finset.mul_sum]
  change (∑ ω, μ ω *
    (‖eta‖^2-2*(∑ i,triangle i*err ω i)-2*A/(δ*(n:ℝ))-(∑ i,W i*residual ω i))) ≤ _ at hh
  rw [heq] at hh
  linarith

theorem ordered_leakage (P : ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hP : ∀ j,j<n → ∀ v,‖P j v‖ ≤ ‖v‖)
    (eta g : H) (horth : ⟪eta,g⟫=0)
    (energy pair err residual : Fin n → ℝ) (A δ : ℝ) (hA : 0≤A) (hδ : 0<δ)
    (henergy : ∀ i,0≤energy i)
    (hpair : ∀ i,(pair i)^2 ≤ A*energy i)
    (happrox : ∀ i : Fin n,⟪P i eta,P i (eta+g)⟫ ≤ err i+pair i)
    (henergy_loss : ∀ i,2*δ*energy i ≤
      ‖P i (eta+g)‖^2-‖P (i+1) (eta+g)‖^2+residual i) :
    ‖eta‖^2-2*(∑ i,triangle i*err i)-2*A/(δ*(n:ℝ))-
      (∑ i,(∑ j,if j ≤ i then triangle j else 0)*residual i) ≤
      ‖eta+g‖^2-‖P n (eta+g)‖^2 := by
  let u : ℕ → ℝ := fun j => ‖P j (eta+g)‖^2
  have hp : ∀ i : Fin n,‖eta‖^2-2*err i-2*pair i ≤ ‖eta+g‖^2-u i := by
    intro i
    have h := contraction_loss_lower (P i) eta g horth
      (hP i i.isLt g)
    dsimp only [u]
    linarith [happrox i]
  have ht : ∀ i : Fin n,(‖eta+g‖^2-u i)+
      (∑ j : Fin n,if i ≤ j then u j-u (j+1) else 0) ≤
      ‖eta+g‖^2-u n := by
    intro i
    rw [suffix_telescope_fin]
    linarith
  have h := finite_future_loss hn (fun i => ‖eta+g‖^2-u i) energy
    (fun i => u i-u (i+1)) residual (fun i => 2*err i) pair
    (‖eta‖^2) (‖eta+g‖^2-u n) A δ hA hδ henergy hpair henergy_loss hp ht
  have he : (∑ i : Fin n,triangle i*(2*err i)) = 2*(∑ i,triangle i*err i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  exact h

theorem expected_ordered_leakage (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1)
    (P : Ω → ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hP : ∀ ω j,j<n → ∀ v,‖P ω j v‖ ≤ ‖v‖)
    (eta : H) (g : Ω → H) (horth : ∀ ω,⟪eta,g ω⟫=0)
    (energy pair err residual : Ω → Fin n → ℝ) (A δ E B : ℝ)
    (hA : 0≤A) (hδ : 0<δ) (hB : 0≤B)
    (henergy : ∀ ω i,0≤energy ω i)
    (hpair : ∀ ω i,(pair ω i)^2 ≤ A*energy ω i)
    (happrox : ∀ ω (i : Fin n),⟪P ω i eta,P ω i (eta+g ω)⟫ ≤ err ω i+pair ω i)
    (henergy_loss : ∀ ω i,2*δ*energy ω i ≤
      ‖P ω i (eta+g ω)‖^2-‖P ω (i+1) (eta+g ω)‖^2+residual ω i)
    (herr : ∀ i,∑ ω,μ ω*err ω i ≤ E)
    (hres : ∀ i,∑ ω,μ ω*residual ω i ≤ B) :
    ‖eta‖^2-2*E-2*A/(δ*(n:ℝ))-(n:ℝ)*B ≤
      ∑ ω,μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (ordered_leakage (P ω) n hn (hP ω) eta (g ω)
      (horth ω) (energy ω) (pair ω) (err ω) (residual ω) A δ hA hδ
      (henergy ω) (hpair ω) (happrox ω) (henergy_loss ω)) (hμ ω))
  let W : Fin n → ℝ := fun i => ∑ j,if j ≤ i then triangle j else 0
  have swap (f : Ω → Fin n → ℝ) (w : Fin n → ℝ) :
      (∑ ω,μ ω*(∑ i,w i*f ω i))=∑ i,w i*(∑ ω,μ ω*f ω i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have he : (∑ ω,μ ω*(∑ i,triangle i*err ω i)) ≤ E := by
    rw [swap]
    calc
      _ ≤ ∑ i,triangle i*E := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (herr i) (triangle_nonneg i))
      _ = E := by rw [←Finset.sum_mul,triangle_sum hn,one_mul]
  have hr : (∑ ω,μ ω*(∑ i,W i*residual ω i)) ≤ (n:ℝ)*B := by
    rw [swap]
    calc
      _ ≤ ∑ i,W i*B := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hres i) (triangle_prefix_pos i).le)
      _ ≤ ∑ _i : Fin n,B := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left hB (triangle_prefix_le_one hn i))
      _ = _ := by simp
  have heq : (∑ ω, μ ω *
      (‖eta‖^2-2*(∑ i,triangle i*err ω i)-2*A/(δ*(n:ℝ))-(∑ i,W i*residual ω i))) =
      ‖eta‖^2-2*(∑ ω,μ ω*(∑ i,triangle i*err ω i))-2*A/(δ*(n:ℝ))-
        (∑ ω,μ ω*(∑ i,W i*residual ω i)) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul]
    simp only [mul_left_comm (μ _) (2:ℝ),←Finset.mul_sum]
  change (∑ ω, μ ω *
    (‖eta‖^2-2*(∑ i,triangle i*err ω i)-2*A/(δ*(n:ℝ))-(∑ i,W i*residual ω i))) ≤ _ at hh
  rw [heq] at hh
  linarith

end

open scoped RealInnerProductSpace
variable {Ω H : Type*} [Fintype Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
lemma mean_square_le (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1) (f : Ω → ℝ) :
    (∑ ω,μ ω*f ω)^2 ≤ ∑ ω,μ ω*(f ω)^2 := by
  let m : ℝ := ∑ ω,μ ω*f ω
  have hz : 0≤∑ ω,μ ω*(f ω-m)^2 := Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (sq_nonneg _))
  have he : (∑ ω,μ ω*(f ω-m)^2)=(∑ ω,μ ω*(f ω)^2)-m^2 := by
    have hterm (ω : Ω) : μ ω*(f ω-m)^2=μ ω*(f ω)^2-2*m*(μ ω*f ω)+m^2*μ ω := by ring
    simp_rw [hterm,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    rw [hs]
    change (∑ ω,μ ω*(f ω)^2)-2*m*m+m^2*1= _
    ring
  rw [he] at hz
  exact sub_nonneg.mp hz

theorem expected_ordered_leakage_moments
    (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1)
    (P : Ω → ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hP : ∀ ω j,j<n → ∀ v,‖P ω j v‖≤‖v‖)
    (eta : H) (g : Ω → H) (horth : ∀ ω,⟪eta,g ω⟫=0)
    (energy pair err : Ω → Fin n → ℝ) (A δ E B : ℝ)
    (hA : 0≤A) (hδ : 0<δ) (hB : 0≤B)
    (henergy : ∀ ω i,0≤energy ω i)
    (hpair : ∀ ω i,(pair ω i)^2≤A*energy ω i)
    (happrox : ∀ ω (i : Fin n),⟪P ω i eta,P ω i (eta+g ω)⟫≤err ω i+pair ω i)
    (hloss : ∀ i : Fin n, 2*δ*(∑ ω,μ ω*energy ω i) ≤
      (∑ ω,μ ω*(‖P ω i (eta+g ω)‖^2-‖P ω (i+1) (eta+g ω)‖^2))+B)
    (herr : ∀ i,∑ ω,μ ω*err ω i≤E) :
    ‖eta‖^2-2*E-2*A/(δ*(n:ℝ))-(n:ℝ)*B ≤
      ∑ ω,μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2) := by
  let u : ℕ → ℝ := fun j=>∑ ω,μ ω*‖P ω j (eta+g ω)‖^2
  let u₀ : ℝ := ∑ ω,μ ω*‖eta+g ω‖^2
  let q : Fin n → ℝ := fun i=>∑ ω,μ ω*pair ω i
  let e : Fin n → ℝ := fun i=>∑ ω,μ ω*energy ω i
  have hq (i : Fin n) : (q i)^2≤A*e i := by
    apply (mean_square_le μ hμ hs (fun ω=>pair ω i)).trans
    calc
      _ ≤ ∑ ω,μ ω*(A*energy ω i) := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpair ω i) (hμ ω))
      _ = A*e i := by simp only [e,mul_left_comm (μ _) A,Finset.mul_sum]
  have he (i : Fin n) : 0≤e i := Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (henergy ω i))
  have hp (i : Fin n) : ‖eta‖^2-2*E-2*q i≤u₀-u i := by
    have hpt (ω : Ω) : ‖eta‖^2-2*err ω i-2*pair ω i ≤
        ‖eta+g ω‖^2-‖P ω i (eta+g ω)‖^2 := by
      have h := contraction_loss_lower (P ω i) eta (g ω) (horth ω) (hP ω i i.isLt (g ω))
      linarith [happrox ω i]
    have ht := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hμ ω))
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul] at ht
    simp only [mul_left_comm (μ _) (2:ℝ),←Finset.mul_sum] at ht
    change ‖eta‖^2-2*(∑ ω,μ ω*err ω i)-2*q i≤u₀-u i at ht
    linarith [herr i]
  have hel (i : Fin n) : 2*δ*e i≤u i-u (i+1)+B := by
    simpa only [u,e,mul_sub,Finset.sum_sub_distrib] using hloss i
  have ht (i : Fin n) : (u₀-u i)+(∑ j : Fin n,if i≤j then u j-u (j+1) else 0)≤u₀-u n := by
    rw [suffix_telescope_fin]
    linarith
  have h := finite_future_loss hn (fun i=>u₀-u i) e (fun i=>u i-u (i+1))
    (fun _=>B) (fun _=>2*E) q (‖eta‖^2) (u₀-u n) A δ hA hδ he hq hel hp ht
  have her : (∑ i : Fin n,triangle i*(2*E))=2*E := by rw [←Finset.sum_mul,triangle_sum hn,one_mul]
  have hr : (∑ i : Fin n, (∑ j : Fin n, if j ≤ i then triangle j else 0) * B) ≤ (n : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin n,B := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left hB (triangle_prefix_le_one hn i))
      _ = _ := by simp
  rw [her] at h
  have hf : u₀-u n=(∑ ω,μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2)) := by
    simp only [u₀,u,mul_sub,Finset.sum_sub_distrib]
  rw [←hf]
  linarith

end Heisenberg.FiniteLeakage

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SpatialFrame Heisenberg.Exposure
variable {k : ℕ}

theorem routed_mean_leakage (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (Ω I B : Type*) [Fintype Ω] [Fintype I]
      [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (H : Ω → ℕ → Set (Slots (B:=B) Λ))
      (x : I → ZSite k) (R : ℕ)
      (μ : Ω → ℝ) (eta : EuclideanSpace ℝ (Slots (B:=B) Λ))
      (g : Ω → EuclideanSpace ℝ (Slots (B:=B) Λ))
      (P : Ω → ℕ → EuclideanSpace ℝ (Slots (B:=B) Λ) →ₗ[ℝ]
        EuclideanSpace ℝ (Slots (B:=B) Λ))
      (K : Ω → ℕ → Slots (B:=B) Λ → I → ℝ)
      (a b : ℕ → Slots (B:=B) Λ) (q n : ℕ) (e : Fin q ≃ Edges Step Λ)
      (δ ρ ζ rem : ℝ),
      0 < n → 0 < δ → 0 ≤ rem →
      (∀ i : Fin q, a i = (e i).val.1) → (∀ i : Fin q, b i = (e i).val.2) →
      F ⊆ Λ → (∀ z ∈ F, ∀ w, Step z w → w ∈ Λ) →
      (∀ ω, 0 ≤ μ ω) → (∑ ω, μ ω = 1) →
      (∀ ω, ⟪eta,g ω⟫ = 0) →
      (∀ ω j, j < n → ∀ v, ‖P ω j v‖ ≤ ‖v‖) →
      (∀ ω (i : Fin n) j, j.1.val ∉ F → (P ω i (eta+g ω)).ofLp j = 0) →
      (∀ ω (i : Fin n) j, 0 ≤ (P ω i (eta+g ω)).ofLp j ∧
        (P ω i (eta+g ω)).ofLp j ≤ 1) →
      (∀ ω (i : Fin n) j l, 0 ≤ K ω i j l) →
      (∀ ω (i : Fin n) l, ∑ j, K ω i j l ≤ 1) →
      (∀ z r, 0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card : ℝ)
        ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ ω (i : Fin n) j l, K ω i j l ≠ 0 → j ∈ H ω i) →
      (∀ ω (i : Fin n), ⟪P ω i eta, P ω i (eta+g ω)⟫ =
        ∑ l, ∑ j, K ω i j l*(P ω i (eta+g ω)).ofLp j) →
      (∀ (i : Fin n) l, (∑ ω, μ ω*(if ¬Regular (blocked Λ (H ω i)) (x l) R M
        (1/(100*(k+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
      (∀ (i : Fin n) l, (∑ ω, μ ω*(∑ j, if (R:ℝ)<dist j.1.val (x l)
        then K ω i j l else 0)) ≤ ζ) →
      (∀ i : Fin n, 2*δ*(∑ ω, μ ω*quietEnergy (H ω i) a b q (P ω i (eta+g ω))) ≤
        (∑ ω, μ ω*(‖P ω i (eta+g ω)‖^2-‖P ω (i+1) (eta+g ω)‖^2))+rem) →
      ‖eta‖^2-2*((ρ+ζ)*Fintype.card I)-
        2*(C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I)/(δ*(n:ℝ))-(n:ℝ)*rem ≤
      ∑ ω, μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2) := by
  obtain ⟨M,C,hC,hroute⟩ := routed_sweep_pair hk L hL
  refine ⟨M,C,hC,?_⟩
  intro Ω I B _ _ _ _ Λ F H x R μ eta g P K a b q n e δ ρ ζ rem hn hδ hrem
    ha hb hF hframe hμ hs horth hP hsup hv hK hm hg hKH hrep hbad hesc hloss
  let energy : Ω → Fin n → ℝ := fun ω i => quietEnergy (H ω i) a b q (P ω i (eta+g ω))
  let pair : Ω → Fin n → ℝ := fun ω i => ∑ l, ∑ j,
    goodMass (K ω i) x (fun j => j.1.val) (blocked Λ (H ω i)) R M l j *
      (P ω i (eta+g ω)).ofLp j
  let err : Ω → Fin n → ℝ := fun ω i =>
    (∑ l, if ¬Regular (blocked Λ (H ω i)) (x l) R M (1/(100*(k+1:ℝ)))
      then (1:ℝ) else 0) +
    (∑ l, ∑ j, if (R:ℝ)<dist j.1.val (x l) then K ω i j l else 0)
  have he (ω : Ω) (i : Fin n) : 0 ≤ energy ω i := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact sq_nonneg _
    · rfl
  have hp (ω : Ω) (i : Fin n) : (pair ω i)^2 ≤
      (C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I)*energy ω i := by
    exact hroute I B Λ F (H ω i) x (K ω i) (P ω i (eta+g ω)) R a b q e ha hb
      hF hframe (hsup ω i) (hK ω i) (hm ω i) hg (hKH ω i) (fun j => (hv ω i j).1)
  have happ (ω : Ω) (i : Fin n) : ⟪P ω i eta,P ω i (eta+g ω)⟫ ≤ err ω i+pair ω i := by
    rw [hrep]
    exact kernel_pairing_split (K ω i) (hK ω i) (hm ω i) x (fun j => j.1.val)
      (blocked Λ (H ω i)) R M (P ω i (eta+g ω)).ofLp (hv ω i)
  have herr (i : Fin n) : (∑ ω, μ ω*err ω i) ≤ (ρ+ζ)*Fintype.card I := by
    simp only [err,mul_add (μ _) _ _,Finset.sum_add_distrib,Finset.mul_sum]
    conv_lhs => lhs; rw [Finset.sum_comm]
    conv_lhs => rhs; rw [Finset.sum_comm]
    have h₁ := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => hbad i l)
    have h₂ := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => hesc i l)
    simp only [Finset.mul_sum] at h₂
    calc
      _ ≤ (∑ _l : I, ρ)+(∑ _l : I, ζ) := add_le_add h₁ h₂
      _ = _ := by simp; ring
  exact Heisenberg.FiniteLeakage.expected_ordered_leakage_moments μ hμ hs P n hn hP eta g horth
    energy pair err (C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I) δ
    ((ρ+ζ)*Fintype.card I) rem (by positivity) hδ hrem he hp happ hloss herr

end Heisenberg.Flow

end

end OAI
