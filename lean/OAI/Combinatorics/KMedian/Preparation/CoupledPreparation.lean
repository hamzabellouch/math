import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationOuter
import OAI.Combinatorics.KMedian.Preparation.PreparationInner
import OAI.Combinatorics.KMedian.Preparation.RetainedActivations

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset WeightedRounding
variable {E T I : Type} [Fintype E] [DecidableEq E]
  [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I]

structure CoupledLaw (D : E → Finset T) (a w : E → ℝ) (P : T → Finset I)
    (y : I → ℝ) (p c : T → ℝ) (g γ B : ℝ) (Δ : ℕ) where
  Ω : Type
  [finite : Fintype Ω]
  ν : FiniteLaw Ω
  κ : Ω → FiniteLaw (T → Finset I)
  O : Ω → E → ℕ
  N : Ω → E → ℝ
  R : Ω → T → E → ℕ
  K : Ω → T → ℕ
  C : Ω → (T → Finset I) → T × I → ℕ
  open_cap : ∀ ω, 0 < ν.weight ω → ∀ e, w e ≤ 1 → g*(O ω e:ℝ) ≤ 1
  open_zero : ∀ ω, 0 < ν.weight ω → ∀ e, w e=0 → O ω e=0
  nominal_nonneg : ∀ ω, 0 < ν.weight ω → ∀ e, 0 ≤ N ω e
  nominal_cap : ∀ ω, 0 < ν.weight ω → ∀ e, N ω e ≤ g*(O ω e:ℝ)
  nominal_mean : ∀ e, ν.expect (fun ω => N ω e)=w e
  nominal_variance : ∀ e, ν.variance (fun ω => N ω e) ≤ g*w e
  nominal_pair : ∀ e f, e ≠ f → ν.expect (fun ω => N ω e*N ω f) ≤ w e*w f
  request_cap : ∀ ω, 0 < ν.weight ω → ∀ t e, R ω t e ≤ O ω e
  request_target : ∀ ω t e, t ∉ D e → R ω t e=0
  request_mean : ∀ t e, ν.expect (fun ω => g*(R ω t e:ℝ)) ≤ if t ∈ D e then w e else 0
  exact_total : ∀ ω t, K ω t+(∑ e, R ω t e)=Δ
  half : ∀ ω t, (1/2:ℝ) ≤ g*(K ω t:ℝ)
  total_cap : ∀ ω t, K ω t ≤ Δ
  total_deviation : ∀ t, ν.expect (fun ω => |g*(K ω t:ℝ)-p t|) ≤ γ*c t+Real.sqrt (g*(1+γ)*c t)
  pieces : ∀ ω ξ, 0 < (κ ω).weight ξ → ∀ t,
    (∑ i, C ω ξ (t,i))=K ω t ∧ (∀ i, C ω ξ (t,i) ≤ Δ) ∧
    (∀ i, i ∉ P t → C ω ξ (t,i)=0)
  piece_mean : ∀ ω t i, (κ ω).expect (fun ξ => g*(C ω ξ (t,i):ℝ))=
    if i ∈ P t then (g*(K ω t:ℝ))*y i/p t else 0
  piece_pair : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => (g*(C ω ξ a:ℝ))*(g*(C ω ξ b:ℝ))) ≤
    (if a.2 ∈ P a.1 then (g*(K ω a.1:ℝ))*y a.2/p a.1 else 0)*
    (if b.2 ∈ P b.1 then (g*(K ω b.1:ℝ))*y b.2/p b.1 else 0)
  piece_variance : ∀ ω a, (κ ω).variance (fun ξ => g*(C ω ξ a:ℝ)) ≤
    g*(if a.2 ∈ P a.1 then (g*(K ω a.1:ℝ))*y a.2/p a.1 else 0)
  budget : 1-4*g*(1+γ)/γ ≤ ν.prob (fun ω =>
    (∑ e, a e*(g*(O ω e:ℝ)))+(∑ t, g*(K ω t:ℝ)) ≤ B+3*g)

theorem coupled_law (D : E → Finset T) (a w : E → ℝ) (P : T → Finset I)
    (y : I → ℝ) (p c : T → ℝ) {g γ B : ℝ} {Δ : ℕ}
    (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (ha0 : ∀ e, 0 ≤ a e) (ha1 : ∀ e, a e ≤ 1) (hw : ∀ e, 0 ≤ w e)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t) (hpunit : ∀ t, p t+c t=1)
    (hmass : ∀ t, ∑ i ∈ P t, y i=p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8)
    (htarget : ∀ t, (∑ e, if t ∈ D e then w e else 0)=(1+γ)*c t)
    (hplanned : (Fintype.card T:ℝ)+(∑ e, (a e-((D e).card:ℝ))*w e)=B-γ*∑ t, c t) :
    Nonempty (CoupledLaw D a w P y p c g γ B Δ) := by
  classical
  obtain ⟨Ω,inst,hex⟩ := outer_grid_law D a w c hg hγ hγ1 heven hunit ha0 ha1 hw hc0 hc1 htarget hplanned
  let := inst
  obtain ⟨ν,m,S,O,N,K,hs,hNm,hNv,hNp,hAm,hZ,hK,hbudget⟩ := hex
  let A := fun ω t e => activationCount D m S t e ω
  obtain ⟨R,hRA,hRsum⟩ := retained_table A Δ
  let O' := fun ω e => ⌊O ω e⌋₊
  have hOf : ∀ ω, 0 < ν.weight ω → ∀ e, (O' ω e:ℝ)=O ω e := by
    intro ω hω e
    rcases (hs ω hω).2.1 e with he | he
    · simp only [O',he,Nat.floor_natCast]
    · have he' : O ω e=((m e+1:ℕ):ℝ) := by simpa only [Nat.cast_add,Nat.cast_one] using he
      simp only [O',he',Nat.floor_natCast]
  have hKC : ∀ ω t, K ω t ≤ Δ := by
    intro ω t
    have he : g*(K ω t:ℝ) ≤ g*(Δ:ℝ) := (hK ω t).2.2.trans_eq hunit.symm
    exact_mod_cast ((mul_le_mul_iff_right₀ hg).mp he)
  choose κ C hCs hCm hCp hCv hC0 hC1 using fun ω =>
    rescaled_bundle_law P y p (K ω) Δ hg hunit hy hp hmass (hKC ω)
  have hRtotal : ∀ ω t, K ω t+(∑ e, R ω t e)=Δ := by
    intro ω t
    have hc := (grid_clip hg heven hunit (∑ e, A ω t e)).1
    have he : g*(K ω t:ℝ)+g*((∑ e, R ω t e):ℕ)=1 := by
      rw [hRsum,← hc,(hK ω t).1,deficit_cast]
      dsimp only [A]
      ring
    have he' : (((K ω t+(∑ e, R ω t e):ℕ)):ℝ)=(Δ:ℝ) := by
      apply mul_left_cancel₀ hg.ne'
      rw [Nat.cast_add,mul_add,hunit]
      exact he
    exact_mod_cast he'
  refine ⟨{
    Ω := Ω
    finite := inst
    ν := ν
    κ := κ
    O := O'
    N := fun ω e => g*N ω e
    R := R
    K := K
    C := C
    open_cap := ?_
    open_zero := ?_
    nominal_nonneg := ?_
    nominal_cap := ?_
    nominal_mean := hNm
    nominal_variance := hNv
    nominal_pair := hNp
    request_cap := ?_
    request_target := ?_
    request_mean := ?_
    exact_total := hRtotal
    half := fun ω t => (hK ω t).2.1
    total_cap := hKC
    total_deviation := ?_
    pieces := hCs
    piece_mean := hCm
    piece_pair := hCp
    piece_variance := hCv
    budget := ?_ }⟩
  · intro ω hω e he
    rw [hOf ω hω e]
    exact (hs ω hω).2.2.2.2.1 e he
  · intro ω hω e he
    have hz : (O' ω e:ℝ)=0 := by
      rw [hOf ω hω e]
      exact (hs ω hω).2.2.2.1 e he
    exact_mod_cast hz
  · intro ω hω e
    apply mul_nonneg hg.le
    rcases (hs ω hω).2.2.1 e with he | he <;> rw [he] <;> positivity
  · intro ω hω e
    rw [hOf ω hω e]
    exact mul_le_mul_of_nonneg_left ((hs ω hω).2.2.2.2.2.1 e) hg.le
  · intro ω hω t e
    apply (hRA ω t e).trans
    have he : (A ω t e:ℝ) ≤ (O' ω e:ℝ) := by
      rw [hOf ω hω e]
      dsimp only [A]
      rw [activationCount_cast]
      unfold activation
      split_ifs
      · exact (hs ω hω).2.2.2.2.2.2 e t
      · exact (hOf ω hω e) ▸ Nat.cast_nonneg _
    exact_mod_cast he
  · intro ω t e ht
    have he : A ω t e=0 := by simp only [A,activationCount,ite_eq_right ht]
    exact Nat.eq_zero_of_le_zero (he ▸ hRA ω t e)
  · intro t e
    calc
      _ ≤ ν.expect (fun ω => g*(A ω t e:ℝ)) := ν.expect_mono (fun ω =>
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hRA ω t e)) hg.le)
      _ = _ := hAm e t
  · intro t
    have hc : c t ≤ 1/2 := by linarith only [hc1 t]
    have h := FiniteLaw.rescaling_noise ν (deficit D m S g t) (hc0 t) hc hγ.le hg.le
      (hZ t).1 (hZ t).2
    have he : (fun ω => |g*(K ω t:ℝ)-p t|)=
        (fun ω => |min (deficit D m S g t ω) (1/2)-c t|) := by
      funext ω
      rw [(hK ω t).1]
      have he' : 1-min (deficit D m S g t ω) (1/2)-p t=
          -(min (deficit D m S g t ω) (1/2)-c t) := by linarith only [hpunit t]
      rw [he',abs_neg]
    rw [he]
    simpa only [abs_sub_comm] using h
  · apply hbudget.trans
    apply ν.prob_mono_support
    intro ω hω he
    have heq : (∑ e, a e*(g*(O' ω e:ℝ)))=g*∑ e, a e*O ω e := by
      simp_rw [hOf ω hω]
      rw [mul_sum]
      exact sum_congr rfl (fun _ _ => by ring)
    rwa [heq]

end MetricKMedian.Preparation
end
end

end OAI
