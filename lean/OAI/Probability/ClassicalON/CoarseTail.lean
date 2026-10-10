import OAI.Probability.ClassicalON.CoarsePaths

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

def codeEvent (G : LatticeGraph) (N : ℤ) (t : ℕ) (z : Site) (c : CoarseCode (25*t))
    (η : G.edges → Bool) : ℝ :=
  ∏ i : {i : Fin (25*t+1) // siteColor (codePosition z c i)=codeColor t z c},
    G.annulusIndicator N (coarseCenter N (codePosition z c i.val)) η

theorem codeEvent_nonneg (G : LatticeGraph) (N : ℤ) (t : ℕ) (z : Site) (c : CoarseCode (25*t))
    (η : G.edges → Bool) : 0≤G.codeEvent N t z c η :=
  Finset.prod_nonneg (fun _ _ => G.annulusIndicator_nonneg _ _ _)

def connectionProbability (G : LatticeGraph) (b : G.edges → ℝ) (x y : G.vertices) : ℝ :=
  freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (fun η => if bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y then 1 else 0)

theorem connectionProbability_le_one (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e,0≤b e) (x y : G.vertices) :
    G.connectionProbability b x y≤1 := by
  unfold connectionProbability
  calc
    _≤freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (fun _ => 1) := by
      apply freeBondMean_mono _ _ _ hb
      intro η
      split_ifs <;> norm_num
    _=1 := freeBondMean_one _ _ _

theorem connection_le_codeSum (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e,0≤b e)
    (x y : G.vertices) (N : ℤ) (hN : 0<N) (t : ℕ)
    (hfar : N*((25*t:ℕ)+4)≤ siteRadius x.val y.val) :
    G.connectionProbability b x y≤
      ∑ c : SimpleCoarseCode (coarseSite N x.val) (25*t),
        freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (G.codeEvent N t (coarseSite N x.val) c.val) := by
  rw [← freeBondMean_sum]
  apply freeBondMean_mono _ _ _ hb
  intro η
  split_ifs with hxy
  · obtain ⟨c,hc⟩ := G.connected_code_crossings η x y N hN (25*t) hfar hxy
    have he : G.codeEvent N t (coarseSite N x.val) c.val η=1 := by
      unfold codeEvent
      simp only [hc,Finset.prod_const_one]
    rw [← he]
    exact Finset.single_le_sum (fun c _ => G.codeEvent_nonneg _ _ _ c.val η) (Finset.mem_univ c)
  · exact Finset.sum_nonneg (fun c _ => G.codeEvent_nonneg _ _ _ c.val η)

theorem connection_geometric_tail (β : ℝ) (hβ : 0≤β) :
    ∃ N : ℕ,0<N ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (x y : G.vertices) (t : ℕ),(N:ℤ)*((25*t:ℕ)+4)≤ siteRadius x.val y.val →
        G.connectionProbability b x y≤(1/2:ℝ)^t := by
  let ε : ℝ := (1/2)/(9:ℝ)^25
  have hε : 0<ε := by positivity
  have hε1 : ε≤1 := by norm_num [ε]
  obtain ⟨k,hk,hs⟩ := separated_annuli_small β hβ ε hε
  refine ⟨2^k,by positivity,?_⟩
  intro G b hb x y t hfar
  have hN : (0:ℤ)<(2^k:ℕ) := by positivity
  apply le_trans (G.connection_le_codeSum b (fun e => (hb e).1) x y _ hN t hfar)
  calc
    _≤∑ _c : SimpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t),ε^t := by
      apply Finset.sum_le_sum
      intro c _
      have hh := hs G b hb {i : Fin (25*t+1) // siteColor (codePosition (coarseSite (2^k:ℕ) x.val) c.val i)=
        codeColor t (coarseSite (2^k:ℕ) x.val) c.val}
        (fun i => coarseCenter (2^k:ℕ) (codePosition (coarseSite (2^k:ℕ) x.val) c.val i.val))
        (sameColor_separated _ hN _ c.property _)
      apply le_trans hh
      exact pow_le_pow_of_le_one (le_of_lt hε) hε1 (codeColor_card t _ c.val)
    _=(Fintype.card (SimpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t)):ℝ)*ε^t := by simp
    _≤(9:ℝ)^(25*t)*ε^t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_simpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t)
    _=(1/2:ℝ)^t := by
      rw [pow_mul,← mul_pow]
      congr 1
      dsimp [ε]
      field_simp

end ClassicalON.LatticeGraph

end

end OAI
