import OAI.MathematicalPhysics.Transonic.Exterior.Step

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset FixedInterval
namespace NormalizedTrace

structure Trace where
  (b r sc sr num den : ℕ → Box)
  (rel sq cu qu : ℕ → ℕ → Box)

structure ValidRow (Q : ℤ) (D n : ℕ) (a : Weights) (t : Trace) : Prop where
  rel_self : t.rel n (n-1)=oneBox Q
  rel_step : ∀ j, 1≤j → j<n-1 → t.rel n j=divBox Q (t.rel n (j+1)) (t.r (j+1))
  sc : t.sc n=squareBox Q D t.b (t.rel n) n
  sr : t.sr n=squareRestBox Q D t.b (t.rel n) n
  sq : ∀ j, n-2≤j → j≤n → t.sq n j=power2Box Q t.sc (t.rel n) j
  cu : ∀ j, n-2≤j → j≤n+1 → t.cu n j=power3Box Q D t.b (t.rel n) t.sc j
  qu : ∀ j, n-1≤j → j≤n → t.qu n j=power4Box Q D t.b (t.rel n) t.sc j
  num : t.num n=stepBox Q a n (t.sq n) (t.cu n) (t.qu n) (t.sr n)

lemma row_enclosed {Q : ℤ} (hQ : 0<Q) (D n : ℕ) (hn : 2≤n) (hd : n≤2^D)
    (a : Weights) (h sigma kappa c : ℝ) (ha : WeightsHold Q a h sigma kappa c)
    (t : Trace) (hv : ValidRow Q D n a t) (w : Series) (hw : coeff 0 w=0)
    (hb : ∀ j, 1≤j → j<n → Holds Q (t.b j) (coeff j w))
    (hbpos : ∀ j, 1≤j → j<n → 0<(t.b j).center-(t.b j).radius)
    (hr : ∀ j, 2≤j → j<n → Holds Q (t.r j) (coeff j w/coeff (j-1) w))
    (hrpos : ∀ j, 2≤j → j<n → 0<(t.r j).center-(t.r j).radius)
    (hsc : ∀ j, 2≤j → j<n → Holds Q (t.sc j) (squareRatio w j)) :
    Holds Q (t.sc n) (squareRatio w n) ∧
    Holds Q (t.num n) (scaledRatioStep h sigma kappa c n (powerRatio w (n-1) 2)
      (powerRatio w (n-1) 3) (powerRatio w (n-1) 4) (squareRRatio w n)) := by
  have hb0 : ∀ j, 1≤j → j≤n-1 → coeff j w≠0 := by
    intro j hj hj';exact ne_of_gt (enclosed_pos hQ (hb j hj (by omega)) (hbpos j hj (by omega)))
  have hrel := relative_enclosed hQ (fun j => coeff j w) t.r (t.rel n) (n-1)
    (hb0 (n-1) (by omega) le_rfl)
    (fun j hj hj' => hr j hj (by omega)) (fun j hj hj' => hrpos j hj (by omega))
    hb0 hv.rel_self hv.rel_step
  have hs : Holds Q (t.sc n) (squareRatio w n) := by
    rw [hv.sc]
    exact square_enclosed hQ D n hd t.b (t.rel n) w hw hb (fun j hj hj' => hrel j hj (by omega))
  have hsc' : ∀ j, 2≤j → j≤n → Holds Q (t.sc j) (squareRatio w j) := by
    intro j hj hj';by_cases he : j=n
    · simpa only [he] using hs
    · exact hsc j hj (by omega)
  refine ⟨hs,?_⟩
  rw [hv.num]
  apply stepBox_enclosed hQ a h sigma kappa c ha n (t.sq n) (t.cu n) (t.qu n) (t.sr n)
  · intro j hj hj';rw [hv.sq j hj hj']
    exact power2_enclosed hQ t.sc (t.rel n) w hw (n-1) n j hj' (by omega) hb0 hsc' hrel
  · intro j hj hj';rw [hv.cu j hj hj']
    exact power3_enclosed hQ D t.b (t.rel n) t.sc w hw (n-1) n j (by omega) (by omega) (by omega)
      hb0 (fun j hj hj' => hb j hj (by omega)) hsc' hrel
  · intro j hj hj';rw [hv.qu j hj hj']
    exact power4_enclosed hQ D t.b (t.rel n) t.sc w hw (n-1) n j (by omega) (by omega) (by omega)
      hb0 (fun j hj hj' => hb j hj (by omega)) hsc' hrel
  · rw [hv.sr]
    exact squareRest_enclosed hQ D n hd t.b (t.rel n) w hb (fun j hj hj' => hrel j hj (by omega))

structure Valid (Q : ℤ) (D N : ℕ) (a : Weights) (t : Trace) : Prop where
  row : ∀ n, 2≤n → n≤N → ValidRow Q D n a t
  bpos : ∀ n, 1≤n → n≤N → 0<(t.b n).center-(t.b n).radius
  rpos : ∀ n, 2≤n → n≤N → 0<(t.r n).center-(t.r n).radius
  dpos : ∀ n, 2≤n → n≤N → 0<(t.den n).center-(t.den n).radius
  ratio : ∀ n, 2≤n → n≤N → t.r n=divBox Q (t.num n) (t.den n)
  coeff : ∀ n, 2≤n → n≤N → t.b n=mul Q (t.b (n-1)) (t.r n)

lemma run {Q : ℤ} (hQ : 0<Q) (D N : ℕ) (hd : N≤2^D)
    (a : Weights) (h sigma kappa c s rho : ℝ) (ha : WeightsHold Q a h sigma kappa c)
    (t : Trace) (hv : Valid Q D N a t) (w : Series) (hw0 : coeff 0 w=0)
    (hw1 : coeff 1 w=s) (he : scaledResidual h sigma kappa c w=0)
    (hrho : rho*(2*(1-sigma)*s)=h*(1-c)*(2*kappa+3)-2*(1-sigma)*s)
    (h1 : Holds Q (t.b 1) s)
    (hden : ∀ n, 2≤n → n≤N → Holds Q (t.den n) (2*(1-sigma)*s*(rho-n))) :
    ∀ n, 1≤n → n≤N → Holds Q (t.b n) (coeff n w) ∧
      (2≤n → Holds Q (t.r n) (coeff n w/coeff (n-1) w) ∧ Holds Q (t.sc n) (squareRatio w n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnN
    by_cases hbase : n=1
    · subst n;refine ⟨?_,by omega⟩;rwa [hw1]
    have hn2 : 2≤n := by omega
    have hb : ∀ j, 1≤j → j<n → Holds Q (t.b j) (coeff j w) := by
      intro j hj hj';exact (ih j hj' hj (by omega)).1
    have hrs : ∀ j, 2≤j → j<n → Holds Q (t.r j) (coeff j w/coeff (j-1) w) ∧
        Holds Q (t.sc j) (squareRatio w j) := by
      intro j hj hj';exact (ih j hj' (by omega) (by omega)).2 hj
    have hh := row_enclosed hQ D n hn2 (by omega) a h sigma kappa c ha t (hv.row n hn2 hnN)
      w hw0 hb (fun j hj hj' => hv.bpos j hj (by omega))
      (fun j hj hj' => (hrs j hj hj').1) (fun j hj hj' => hv.rpos j hj (by omega))
      (fun j hj hj' => (hrs j hj hj').2)
    have hbp := hb (n-1) (by omega) (by omega)
    have hb0 : coeff (n-1) w≠0 := ne_of_gt (enclosed_pos hQ hbp (hv.bpos (n-1) (by omega) (by omega)))
    have hd0 := ne_of_gt (enclosed_pos hQ (hden n hn2 hnN) (hv.dpos n hn2 hnN))
    have herec := scaled_normalized_recurrence h sigma kappa c s rho w hw0 hw1 he hrho n hn2 hb0
    have hediv : coeff n w/coeff (n-1) w =
        scaledRatioStep h sigma kappa c n (powerRatio w (n-1) 2) (powerRatio w (n-1) 3)
          (powerRatio w (n-1) 4) (squareRRatio w n)/(2*(1-sigma)*s*(rho-n)) := by
      apply (eq_div_iff hd0).mpr
      simpa only [mul_comm] using herec
    have hr' : Holds Q (t.r n) (coeff n w/coeff (n-1) w) := by
      rw [hv.ratio n hn2 hnN,hediv]
      exact holds_div hQ hh.2 (hden n hn2 hnN) (hv.dpos n hn2 hnN)
    refine ⟨?_,fun _ => ⟨hr',hh.1⟩⟩
    rw [hv.coeff n hn2 hnN]
    convert holds_mul hQ hbp hr' using 1
    field_simp

end NormalizedTrace
end SepticProfile.ExteriorJet

end
end

end OAI
