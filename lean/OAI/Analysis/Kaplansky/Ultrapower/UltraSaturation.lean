import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiFinite
import OAI.Analysis.Kaplansky.Ultrapower.Construction
import OAI.Analysis.Kaplansky.Ultrapower.UltraDiagonal
import OAI.Analysis.Kaplansky.Ultrapower.Quotient

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue
open Filter Topology
open scoped ComplexOrder ENNReal

inductive StarTerm (C : Type*) where
  | var : StarTerm C
  | const : C → StarTerm C
  | add : StarTerm C → StarTerm C → StarTerm C
  | mul : StarTerm C → StarTerm C → StarTerm C
  | neg : StarTerm C → StarTerm C
  | star : StarTerm C → StarTerm C
namespace StarTerm
variable {C D E : Type*}
def eval [Add D] [Mul D] [Neg D] [Star D] (c : C → D) (x : D) : StarTerm C → D
  | .var => x
  | .const a => c a
  | .add p q => eval c x p+eval c x q
  | .mul p q => eval c x p*eval c x q
  | .neg p => -eval c x p
  | .star p => Star.star (eval c x p)
lemma map_eval [Ring D] [StarRing D] [Ring E] [StarRing E]
    {F : Type*} [FunLike F D E] [NonUnitalRingHomClass F D E] [StarHomClass F D E]
    (φ : F) (c : C → D) (x : D) (p : StarTerm C) :
    φ (p.eval c x)=p.eval (fun a => φ (c a)) (φ x) := by
  induction p <;> simp_all [eval,map_star]
end StarTerm

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
instance seq_nontrivial : Nontrivial (Sequences (A:=A) (ι:=ℕ)) := Kaplansky.boundedProduct_nontrivial

variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)
abbrev UltraQuotient := (V.ultra u).FaithfulQuotient
abbrev ultraHom : Sequences (A:=A) (ι:=ℕ) →⋆ₐ[ℂ] V.UltraQuotient u := (V.ultra u).quotientHom
abbrev ultraQ : V.UltraQuotient u → ℝ := (V.ultra u).quotQ

def seqEvalHom (i : ℕ) : Sequences (A:=A) (ι:=ℕ) →⋆ₐ[ℂ] A where
  toFun a := a i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

lemma ultra_q_tendsto (a : Sequences (A:=A) (ι:=ℕ)) :
    Tendsto (fun i => V.q (a i)) u (𝓝 (V.ultraQ u (V.ultraHom u a))) :=
  V.ultra_val_tendsto u (star a*a)

include hu in

lemma ultra_realize {ι : Type*} [Fintype ι] (P : ι → StarTerm (V.UltraQuotient u)) (t : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : V.UltraQuotient u,
      ‖x‖ ≤ 1 ∧ ∀ j, |V.ultraQ u ((P j).eval id x)-t j| < ε) :
    ∃ x : V.UltraQuotient u, ∀ j, V.ultraQ u ((P j).eval id x)=t j := by
  classical
  let W := V.ultra u
  let Q := V.ultraHom u
  have lift (x : V.UltraQuotient u) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x := W.nullIdeal.mk_surjective x
  choose c hc using lift
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose x hx hxt using fun n => h (ε n/2) (half_pos (hε n))
  have liftn (n : ℕ) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x n ∧ ‖a‖ < 2 := by
    obtain ⟨a,ha,hn⟩ := W.nullIdeal.norm_mk_lt (x n) zero_lt_one
    exact ⟨a,ha,hn.trans_le (by linarith [hx n])⟩
  choose a ha han using liftn
  let F (j : ι) (i : ℕ) (b : A) : ℝ := V.q ((P j).eval (fun d => c d i) b)-t j
  have ht (n : ℕ) (j : ι) :
      Tendsto (fun i => F j i (a n i)) u (𝓝 (V.ultraQ u ((P j).eval id (x n))-t j)) := by
    have he' : Q ((P j).eval c (a n))=(P j).eval id (x n) := by
      rw [StarTerm.map_eval Q,ha n]
      congr 2
      funext d
      exact hc d
    have heval (i : ℕ) : ((P j).eval c (a n)) i=(P j).eval (fun d => c d i) (a n i) := by
      have he := StarTerm.map_eval (seqEvalHom (A:=A) i) c (a n) (P j)
      simp only [seqEvalHom] at he
      exact he
    dsimp only [Q] at he'
    have hh := (V.ultra_q_tendsto u ((P j).eval c (a n))).sub_const (t j)
    simpa only [he',heval] using hh
  let s (n : ℕ) := {i | ∀ j, |F j i (a n i)| ≤ ε n}
  have hs (n : ℕ) : s n ∈ u := by
    have hj (j : ι) : ∀ᶠ i in (u : Filter ℕ), |F j i (a n i)| ≤ ε n := by
      have hlt : |V.ultraQ u ((P j).eval id (x n))-t j| < ε n := (hxt n j).trans (by linarith [hε n])
      exact ((ht n j).abs.eventually (eventually_lt_nhds hlt)).mono (fun _ h => h.le)
    exact Filter.eventually_all.mpr hj
  obtain ⟨k,hk,hgood⟩ := ultra_selector u hu s hs
  let b : Sequences (A:=A) (ι:=ℕ) := ⟨fun i => a (k i) i,memℓp_infty
    ⟨2,by rintro _ ⟨i,rfl⟩; exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (a (k i)) i).trans (han (k i)).le⟩⟩
  refine ⟨Q b,?_⟩
  intro j
  have hb : Tendsto (fun i => F j i (b i)) u (𝓝 0) := by
    have hbound : ∀ᶠ i in (u : Filter ℕ), |F j i (b i)| ≤ ε (k i) := by
      filter_upwards [hk (eventually_ge_atTop 1)] with i hi
      exact hgood i (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi)) (k i) le_rfl j
    apply squeeze_zero_norm' _ ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hk)
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound
  have hqb : Q ((P j).eval c b)=(P j).eval id (Q b) := by
    rw [StarTerm.map_eval Q]
    congr 2
    funext d
    exact hc d
  have heval (i : ℕ) : ((P j).eval c b) i=(P j).eval (fun d => c d i) (b i) := by
    exact StarTerm.map_eval (seqEvalHom (A:=A) i) c b (P j)
  dsimp only [Q] at hqb
  have ht' := (V.ultra_q_tendsto u ((P j).eval c b)).sub_const (t j)
  have hz : V.ultraQ u ((P j).eval id (Q b))-t j=0 := by
    apply tendsto_nhds_unique _ hb
    simpa only [hqb,heval] using ht'
  exact sub_eq_zero.mp hz

end KaplanskyConsequences.QuasiValue

end

end OAI
