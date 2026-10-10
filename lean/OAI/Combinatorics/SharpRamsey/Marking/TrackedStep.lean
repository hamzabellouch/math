import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TrackedGeometry

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section
local instance trackFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance trackFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance trackProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance trackDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance trackDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

lemma flag_alphabet_lower (i q : ℕ) [Fact q.Prime] :
    (q:ℝ)^(2*(i+3)-1) ≤ (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) := by
  have hdim : Module.finrank (ZMod q) (Fin (i+4)→ZMod q)=(i+3)+1:=by simp
  have halphabet : (q:ℝ)^(2*(i+3)-1) ≤ (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=by
    have hh : q^(2*(i+3)-1) ≤ Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):=by
      rw [actualFlag_card hdim,Nat.card_zmod]
      have h1 : q^(i+3) ≤ ∑ j∈range ((i+3)+1),q^j:=single_le_sum (by intros;positivity) (mem_range.mpr (by omega))
      have h2 : q^(i+2) ≤ ∑ j∈range (i+3),q^j:=single_le_sum (by intros;positivity) (mem_range.mpr (by omega))
      calc
        _ = q^(i+3)*q^(i+2):=by rw [←pow_add];congr 1;omega
        _ ≤ _:=Nat.mul_le_mul h1 h2
    exact_mod_cast hh
  exact halphabet

lemma tracked_log_budget (i q : ℕ) (σ Δ P : ℝ) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ)
    (hP : 1 ≤ P) (he : exp σ=(q:ℝ)) :
    0 ≤ log P+((i+3:ℕ):ℝ)*σ+Δ ∧
    P*(q:ℝ)^(i+3)*exp Δ ≤ exp (log P+((i+3:ℕ):ℝ)*σ+Δ) ∧
    log P+((i+3:ℕ):ℝ)*σ+Δ-jointJ (ZMod q) (i+3) ≤ Δ+(|log P|+|log 64|) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hP0 : 0 < P:=lt_of_lt_of_le zero_lt_one hP
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  refine ⟨by have:=log_nonneg hP;positivity,?_,?_⟩
  · rw [exp_add,exp_add,exp_log hP0,exp_nat_mul,he]
  · dsimp only [jointJ]
    rw [Nat.card_zmod,log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow,hlogq]
    linarith [le_abs_self (log P),neg_abs_le (log 64)]

lemma flag_context_linear (i q : ℕ) [Fact q.Prime] (σ η c Lstar : ℝ)
    (hσ : 1 ≤ σ) (hη : 0 ≤ η) (hc : 0 < c) (hLs : 0 < Lstar)
    (he : exp σ=(q:ℝ))
    (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
    (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
    (B Λ L : ℝ) (hLL : L ≤ Lstar) (hkn : k ≤ N)
    (hdom : ∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*σ)
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m B Λ L)
    (hmlo : c*(q:ℝ)*σ^(1+η) ≤ m) :
    (m:ℝ)*((i+3:ℕ):ℝ)*σ-(1+|log c|+|log (2*(Lstar*2))|)*m ≤
      entropy (e.μ.map (fun x j=>flagPair (F (e.source x) (e.chosen x j)))) := by
  have hq0 : (0:ℝ) < q:=he ▸ exp_pos _
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hm : 0 < m:=by
    have : (0:ℝ) < m:=(by positivity : (0:ℝ) < c*(q:ℝ)*σ^(1+η)).trans_le hmlo
    exact_mod_cast this
  have halphabet:=flag_alphabet_lower i q
  have : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=Fintype.card_pos_iff.mp (by
    have : (0:ℝ) < (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ):=(pow_pos hq0 _).trans_le halphabet
    exact_mod_cast this)
  let ee:=e.mono (le_refl _) (le_refl _) hLL
  have hh:=ee.tracked_linear stream F flagPair flagPair_injective (by intros;rfl)
    (by omega : 1 ≤ i+3) hm hkn (by norm_num : (0:ℝ) < 2) hLs hq0 hσ hη hc
    hdom hselect hN hmlo halphabet
  have hlogq : log (q:ℝ)=σ:=by rw [←he,log_exp]
  rw [hlogq] at hh
  dsimp only [ee,ContextOutput.mono] at hh
  convert hh using 1 <;> first | ring | congr!

lemma flag_context_occ (i q : ℕ) [Fact q.Prime]
    (Ω : Type) [Fintype Ω] (k m : ℕ) (p : Law Ω)
    (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q)) (B Λ L M : ℝ)
    (hocc : ∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M)
    (e : ContextOutput p (fun x j=>flagPair (F x j)) m B Λ L) :
    ∀ x,e.μ.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j=>covectorTuple (fun j=>flagPair (F (e.source x) (e.chosen x j))) j∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M := by
  intro x _ W
  have hh:=count_injective_restriction (e.chosen x).toEmbedding
    (fun j=>(flagPair (F (e.source x) j)).swap∈orthogonalRectangle Projectivization.rep Projectivization.rep W)
  apply le_trans _ (hocc _ (e.supported x) W)
  convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
  congr!
  congr 2
  ext index
  simp only [orthogonalRectangle,mem_filter,mem_univ,true_and]

theorem eventually_tracked_step (i : ℕ) (η c Lstar P M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hLs : 0 < Lstar)
    (hP : 1 ≤ P) (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (Λ Δ L : ℝ) (R : ℕ),
      0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      0 ≤ Λ → 0 ≤ Δ → 0 < L → L ≤ Lstar →
      Admissible σ η (stageD σ η k Λ Δ) R →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      (e : ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp Δ) Λ L) → c*(q:ℝ)*σ^(1+η) ≤ m →
      ∃ m' : ℕ, (m:ℝ)/(256*classCount i) ≤ m' ∧
        Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m'
          (P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
          (stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ)) ((4*classCount i)*L)) := by
  let A:=1+|log c|+|log (2*(Lstar*2))|
  let B:=|log P|+|log 64|
  have hA : 0 ≤ A:=by dsimp [A];positivity
  have hB : 0 ≤ B:=by dsimp [B];positivity
  filter_upwards [eventually_uniform_step i η c 1 A B M0 hη hηu hc (by norm_num) hA hB hM0,
    eventually_ge_atTop (1:ℝ)] with σ hstep hσ
  intro q _ hq he Ω _ N k m p stream F Λ Δ L R hk hkn hku hΛ hΔ hL hLL had hdom hselect hN hcon hocc e hmlo
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hF:=flag_context_linear i q σ η c Lstar hσ hη.le hc hLs he Ω N k m p stream F
    _ Λ L hLL hkn hdom hselect hN e hmlo
  let G:=fun x j=>flagPair (F (e.source x) (e.chosen x j))
  let J:=log P+((i+3:ℕ):ℝ)*σ+Δ
  obtain ⟨hJ0,hBJ,hJgap⟩:=tracked_log_budget i q σ Δ P hσ0.le hΔ hP he
  have hcons : ∀ x,e.μ.mass x≠0→ScanConsistent ((List.ofFn (G x)).map toScan):=by
    intro x _
    exact scanConsistent_ordered _ (hcon _ (e.supported x)) (e.chosen x)
  have hocc':=flag_context_occ i q Ω k m p F _ Λ L (M0*σ) hocc e
  obtain ⟨m',hmret,⟨out⟩⟩:=hstep q hq he e.X e.Γ m k e.μ e.msg G e.domains Λ Δ J R
    hk hΛ hΔ hku hmlo (by simpa only [one_mul] using (show (m:ℝ) ≤ k by exact_mod_cast e.length_le).trans hku)
    had e.cost hF hJgap (e.log_size hJ0 hBJ)
    (fun x _ j=>e.hit x j) (fun x _ j=>(F (e.source x) (e.chosen x j)).incident) hcons hocc'
  have hs : stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)) ≤
      P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)):=by gcongr
  have hcost : stageD σ η k Λ Δ*σ^(-η/3)*(m:ℝ) ≤ stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ):=by
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast e.length_le)
    unfold stageD
    positivity
  exact ⟨m',hmret,⟨e.compose (out.mono hs hcost (le_refl _)) (by positivity)⟩⟩
end
end SharpLogRamsey.Marking

end

end OAI
