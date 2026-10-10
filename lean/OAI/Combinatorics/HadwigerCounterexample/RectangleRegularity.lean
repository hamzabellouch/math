import OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection

namespace OAI

/-! # Rectangle Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

def thinCut (μ f : Wgt A) (x : A→B) (y : A→C) (ε : ℝ) :=
  ∀ u : Wgt B,(∀ i,|u i|≤1) → ∀ v : Wgt C,(∀ i,|v i|≤1) →
    |avg μ (fun i=> f i*(u (x i)*v (y i)))|≤ ε
def doubleBook {L R : Type} (x : A→B) (y : A→C) (a : B→L) (b : C→R) :=
  fun i => (a (x i),b (y i))
def swab (x : Bool) : ℝ := if x then 1 else -1
theorem swab_abs (x) : |swab x|=1 := by cases x <;> simp [swab]

private theorem sign_mass (w : Wgt A) (f : A→B) (u : Wgt B) (h : ∀ i,|u i|≤1) :
    ∃ y : B→Bool,|avg w (u ∘ f)|≤|avg w (swab ∘ y ∘ f)| := by
  classical
  let p := mapW w f
  let y (i) := decide (0≤p i)
  have he i :
      p i*swab (y i)=|p i| := by
    by_cases hh : 0≤p i <;> simp [swab,y,hh,abs_of_nonneg,abs_of_neg,lt_of_not_ge]
  have hu :
      |avg p u| ≤ ∑ i,|p i| := by
    unfold avg; refine (Finset.abs_sum_le_sum_abs ..).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)).trans_eq (mul_one _)
  have hz : avg p (swab ∘ y) = ∑ i, |p i| := Finset.sum_congr rfl fun i _=> he i
  refine ⟨y,?_⟩
  rw [show avg w (u∘f)=avg p u from (mapW_avg w f u).symm,show avg w (swab∘y∘f)=
    avg p (swab∘y) from (mapW_avg w f (swab ∘ y)).symm]
  exact hu.trans (hz.symm.le.trans (le_abs_self _))

theorem cut_witness (μ f : Wgt A) {x : A→B} {y : A→C} {ε : ℝ} (h : ¬ thinCut μ f x y ε) :
    ∃ (i : B→Bool) (j : C→Bool), ε < |avg μ (fun z=>f z*(swab (i (x z))*swab (j (y z))))| := by
  classical
  unfold thinCut at h
  push Not at h
  obtain ⟨u,hu,v,hv,h⟩ := h
  let Q (u : Wgt B) (v : Wgt C) := avg μ (fun z=>f z*(u (x z)*v (y z)))
  let U z := μ z*f z*v (y z)
  obtain ⟨i,hi⟩ := sign_mass U x u hu
  have hx (u) : Q u v=avg U (u∘x) := Finset.sum_congr rfl (fun z _=>by unfold U Function.comp; ring)
  let V z := μ z*f z*swab (i (x z))
  obtain ⟨j,hj⟩ := sign_mass V y v hv
  have hy (v) : Q (swab ∘ i) v=avg V (v∘y) := Finset.sum_congr rfl (fun z _=>by
    unfold V Function.comp; ring)
  rw [←hx u,show avg U (swab ∘ i ∘ x)=Q (swab ∘ i) v from (hx (swab ∘ i)).symm] at hi
  rw [←hy v,show avg V (swab ∘ j ∘ y)=Q (swab ∘ i) (swab∘j) from (hy (swab ∘ j)).symm] at hj
  exact ⟨i,j, lt_of_lt_of_le h (hi.trans hj)⟩

def weakRank (μ f : Wgt A) (x : A→B) (y : A→C) (δ : ℝ) (R : ℕ) :=
  ∃ l : ℕ,l≤R ∧ ∃ (a:B→Fin l) (b:C→ Fin l),
    thinCut μ (fun i=> f i-banner μ (doubleBook x y a b) f i) x y δ

set_option maxHeartbeats 800000 in
theorem plenty_cuts (δ M : ℝ) (hδ : 0<δ) (hM : 0≤M) :
    ∃ r:ℕ,∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
      (μ f : Wgt A) (x : A→B) (y : A→C),SubLaw μ → (∀ i,|f i| ≤ M) →
        weakRank μ f x y δ r := by
  classical
  obtain ⟨l,hl⟩ := exists_nat_gt (M^2 / δ^2)
  refine ⟨2^l,fun A B C _ _ _ μ f x y hw hf => ?_⟩
  by_contra h
  have hh (i : ℕ) (hi : i≤l) :
      ∃ (a:B→Fin (2^i)) (b:C→Fin (2^i)), i*δ^2 ≤ ode μ (banner μ (doubleBook x y a b) f) := by
    induction i with
    | zero => exact ⟨fun _=>0,fun _=>0, by simpa using ode_nonneg hw.nz _⟩
    | succ i ih =>
      obtain ⟨a,b,he⟩ := ih (by omega)
      let T := doubleBook x y a b
      let d := fun z => f z-banner μ T f z
      obtain ⟨u,v,e⟩ := cut_witness μ d (x:=x) (y:=y) (ε:=δ) (fun p =>
        h ⟨_,Nat.pow_le_pow_right (by decide) (by omega),a,b,p⟩)
      let r := 2^i
      let E : Fin r × Bool ≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [r,pow_succ])
      let a' z := E (a z,u z); let b' z := E (b z,v z)
      let S := doubleBook x y a' b'
      let U (z j : Fin (2^(i+1))) := ((E.symm z).1,(E.symm j).1)
      let V (z j : Fin (2^(i+1))) := swab (E.symm z).2*swab (E.symm j).2
      have hz : uncurry U ∘ S=T := by
        funext i; simp only [doubleBook,a',b',Function.comp_apply,U,S,uncurry_apply_pair,
          Equiv.symm_apply_apply]; rfl
      have hH (i) : uncurry V (S i)=swab (u (x i))*swab (v (y i)) := by
        simp only [S,doubleBook,a',b',V,uncurry_apply_pair,Equiv.symm_apply_apply]
      have hh (i) : |uncurry V (S i)| ≤ 1 := by rw [hH,abs_mul,swab_abs,swab_abs,mul_one]
      have hq := archive_gain hw f S (uncurry U) (uncurry V) hh
      rw [hz] at hq
      have ht : dip μ d (uncurry V ∘ S)=
          avg μ (fun z => d z*(swab (u (x z))*swab (v (y z)))) :=
        avg_congr (fun i _=> congrArg _ (hH i))
      change (dip μ d _)^2≤_ at hq
      rw [←ht] at e
      refine ⟨a',b',?_⟩
      change ↑(i+1)*δ^2≤ode μ (banner μ S f)
      change ↑i*δ^2≤ode μ (banner μ T f) at he
      push_cast
      nlinarith only [he,hq,e,sq_abs (dip μ d (uncurry V ∘ S)),hδ]
  obtain ⟨a,b,he⟩ := hh l le_rfl
  let F := doubleBook x y a b
  have hb := cashbook_bound μ hw.nz F f M hM hf
  have ht := he.trans (ode_upper hw _ M (fun i : A=> hb (F i)))
  exact not_lt_of_ge ht ((div_lt_iff₀ (by positivity)).mp hl)
end HadwigerCounterexample

end

end OAI
