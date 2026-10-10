import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialHeaderCover
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialInputBridge

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry DescriptionHeaders
open scoped Classical BigOperators Topology NNReal
noncomputable section
local instance flat_JoinedSpatialActualCover_1 (q : ℕ) [Fact q.Prime] :
    Finite (Submodule (ZMod q) (Fin 4→ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4→ZMod q) => (W : Set (Fin 4→ZMod q)))
    SetLike.coe_injective
local instance flat_JoinedSpatialActualCover_2 (q : ℕ) [Fact q.Prime] :
    Fintype (Submodule (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

local instance flat_JoinedSpatialActualCover_3 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedSpatialActualCover_4 (q : ℕ) [Fact q.Prime] :
    Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
  letI : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
  exact Fintype.ofFinite _

theorem actual_cover (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3 ≤ q → exp σ=(q:ℝ) →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (n Jmax : ℕ) (P g b τ : ℝ) (L : ℝ≥0) (R p h M : ℕ),
    0 < n → n ≤ U.card → σ^δ ≤ P → P ≤ σ/40 → g ≤ σ/2+C → 0 < p → (p:ℝ) ≤ σ^2 →
    (n:ℝ)=exp (3*σ/2+g) → exp (σ/2-2*g/15) ≤ Jmax →
    (∀ m,0 < m → m ≤ n → n ≤ 2*m → Budget σ P L R (Nat.log 2 m+2) p h) →
    0 ≤ b → 0 < τ → τ ≤ 1/40 → 200*(q:ℝ)*P ≤ n →
    b+log 2+4*P*τ ≤ P/1000000 →
    50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 →
    2*(q:ℝ)*P ≤ M →
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
      (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
      (∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
        (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
        S⊆U → S.card=n → T.Nonempty → S.card ≤ T.card →
        (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
        (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
        (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
          (n:ℝ)/50 ≤ (S∩planePoints W).card) ∨
        (∃ W ∈ caps,(n:ℝ)/4 ≤ (S∩W).card)) ∧
      (caps.card:ℝ) ≤ (n+1:ℕ)*(Jmax+1:ℕ)*
        (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E := by
  filter_upwards [actual_prepared_input δ C hδ] with σ hprep
  intro q _ hq hqexp U n Jmax P g b τ L R p h M hn hnu hP hPu hgu hp hpu hN hJ hbud hb hτ hτu hnlarge hloss herror hM
  dsimp only
  let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
  let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
    log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
  let B := ((Jmax+1:ℕ):ℝ)*
    (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E
  let ms := (range (n+1)).filter (fun m => 0 < m ∧ n ≤ 2*m ∧ m ≤ U.card)
  have hmr (m : ℕ) (hm : m ∈ ms) : 0 < m ∧ m ≤ n ∧ n ≤ 2*m ∧ m ≤ U.card := by
    obtain ⟨hm,hpos,hhalf,hU⟩ := mem_filter.mp hm
    exact ⟨hpos,by have := mem_range.mp hm; omega,hhalf,hU⟩
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hex (m : ℕ) : ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
      (m ∈ ms → (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
        (∀ S,(∃ bs ∈ headers Jmax m,Input U m planePoints bs σ P g (b+log 2) (2*τ)
          (Real.toNNReal ((q:ℝ)/m)) p S) → ∃ W ∈ caps,(m:ℝ)/2 ≤ (S∩W).card) ∧
        (caps.card:ℝ) ≤ B) := by
    by_cases hm : m ∈ ms
    · obtain ⟨hmp,hmn,hnm,hmu⟩ := hmr m hm
      have hmp' : (0:ℝ) < m := by exact_mod_cast hmp
      have hm': (m:ℝ) ≤ n := by exact_mod_cast hmn
      have hnm': (n:ℝ) ≤ 2*m := by exact_mod_cast hnm
      have hc : (Real.toNNReal ((q:ℝ)/m):ℝ)=(Nat.card (ZMod q):ℝ)/m := by
        rw [Nat.card_eq_fintype_card,ZMod.card,Real.coe_toNNReal _ (by positivity)]
      have hdim : Module.finrank (ZMod q) (Fin 4→ZMod q)=4 := by simp
      have hx : exp σ=(Nat.card (ZMod q):ℝ) := by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hqexp
      obtain ⟨caps,hsize,hcap,hcount⟩ := public_header_cover hdim U m hmp hmu planePoints Jmax
        σ P g (b+log 2) (2*τ) L (Real.toNNReal ((q:ℝ)/m)) R p h M hx hc
        (hbud m hmp hmn hnm) (by have := log_pos (by norm_num : (1:ℝ) < 2); linarith)
        (by linarith) (by linarith)
        (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using (show 100*(q:ℝ)*P ≤ m by linarith))
        (by nlinarith) (by simpa only [show (2:ℝ)*P*(2*τ)=4*P*τ by ring] using herror)
        (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hM)
      refine ⟨caps,fun _ => ⟨?_,hcap,?_⟩⟩
      · intro W hW
        obtain ⟨hWU,hWc⟩ := hsize W hW
        exact ⟨hWU,hWc.trans (mul_le_mul_of_nonneg_right hm' (exp_pos _).le)⟩
      · apply hcount.trans
        dsimp only [B,E,H]
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          rw [Nat.card_eq_fintype_card]
          norm_cast
          gcongr
        · apply exp_le_exp.mpr
          have hn' : (0:ℝ) < n := by exact_mod_cast hn
          have hU' : (0:ℝ) < U.card := hn'.trans_le (by exact_mod_cast hnu)
          have hlog : log ((U.card:ℝ)/m) ≤ log (2*U.card/n) := by
            apply log_le_log (by positivity)
            apply (div_le_div_iff₀ hmp' hn').mpr
            nlinarith
          have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
          nlinarith
        · positivity
        · positivity
    · exact ⟨∅,fun h => (hm h).elim⟩
  choose family hf using hex
  let caps := ms.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨m,hm,hW⟩ := mem_biUnion.mp hW
    exact (hf m hm).1 W hW
  · intro S T hSU hSn hT hST hprod hsp
    have hS : S.Nonempty := card_pos.mp (by omega)
    have hNS : (S.card:ℝ)=exp (3*σ/2+g) := by simpa only [hSn] using hN
    rcases hprep q hq hqexp U S T hSU hS hT hST P g b τ p hτ.le hP hPu hgu hp hpu hNS hprod hsp with hh|hh
    · exact Or.inl (by simpa only [hSn] using hh)
    · obtain ⟨S',planes,hsub,hS',hhalf,hplanes,_,hinput⟩ := hh
      have hm : S'.card ∈ ms := by
        apply mem_filter.mpr
        refine ⟨mem_range.mpr ?_,card_pos.mpr hS',?_,card_le_card (hsub.trans hSU)⟩
        · have := card_le_card hsub; omega
        · simpa only [hSn] using hhalf
      have hpl : planes.length ≤ Jmax := by
        exact_mod_cast hplanes.trans hJ
      have hheader := sized_header S' planePoints planes Jmax S'.card hpl le_rfl
      obtain ⟨W,hW,hcap⟩ := (hf S'.card hm).2.1 S' ⟨_,hheader,hinput⟩
      right
      refine ⟨W,mem_biUnion.mpr ⟨_,hm,hW⟩,?_⟩
      have hhalf' : (n:ℝ) ≤ 2*S'.card := by exact_mod_cast (show n ≤ 2*S'.card by omega)
      have hmon : ((S'∩W).card:ℝ) ≤ (S∩W).card := by
        exact_mod_cast (card_le_card (inter_subset_inter hsub (Subset.refl W)))
      linarith
  · have hcount : (caps.card:ℝ) ≤ ∑ m ∈ ms,((family m).card:ℝ) := by exact_mod_cast card_biUnion_le
    calc
      _  ≤  ∑ m ∈ ms,((family m).card:ℝ) := hcount
      _  ≤  ∑ _m ∈ ms,B := sum_le_sum (fun m hm => (hf m hm).2.2)
      _ = (ms.card:ℝ)*B := by simp
      _  ≤  (n+1:ℕ)*B := mul_le_mul_of_nonneg_right (by
        exact_mod_cast (card_filter_le _ _).trans_eq (card_range _)) hB
      _ = _ := by dsimp [B,E,H]; ring

end
end SharpLogRamsey.SpatialPublic

end

end OAI
