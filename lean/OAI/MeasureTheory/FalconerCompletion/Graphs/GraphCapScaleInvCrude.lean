import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphChildrenHSplit
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphConstOneJet
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFiniteHFBound
import OAI.MeasureTheory.FalconerCompletion.Recursion.BlockDepth

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4FullFar
open scoped RealInnerProductSpace
variable {d : ℕ}

lemma graphCapScale_inv_crude {N a p : ℕ} {c₀ sig : ℝ}
    (hc₀ : 0 < c₀) (hsig : 0 ≤ sig) (hp : p ≤ N) :
    (graphCapScale N a p c₀ sig)⁻¹ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  rw [graphCapScale_eq]
  apply (GraphSourceScale.inverse_cap_scale hc₀ (by positivity) (by positivity)).trans
  have hH : (2:ℝ)^((p:ℝ)-a) ≤ (2:ℝ)^N := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast (show (p:ℤ)-a ≤ N by omega))
  have hs : ((2:ℝ)^N)^(-10*sig) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  calc
    _ ≤ c₀⁻¹+(2:ℝ)^N*1 := add_le_add_right (mul_le_mul hH hs (by positivity) (by positivity)) _
    _ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by nlinarith [inv_pos.mpr hc₀]

lemma graphCapGrid_card_crude {N a p : ℕ} {c₀ sig : ℝ}
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hsig : 0 ≤ sig) (hp : p ≤ N) :
    ((sphereCapGridND d (graphCapScale N a p c₀ sig)).card:ℝ) ≤
      (9*(c₀⁻¹+1))^d*((2:ℝ)^N)^d := by
  apply (sphereCapGridND_card_bound (graphCapScale_pos hc₀) ((min_le_left _ _).trans hc₀1)).trans
  calc
    _ ≤ (9*((c₀⁻¹+1)*(2:ℝ)^N))^d :=
      pow_le_pow_left₀ (by positivity [graphCapScale_pos (N:=N) (a:=a) (p:=p) (sig:=sig) hc₀]) (mul_le_mul_of_nonneg_left (graphCapScale_inv_crude hc₀ hsig hp) (by norm_num)) d
    _ = _ := by rw [←mul_assoc,mul_pow]

lemma graphCapGrid_pair_card_crude {N a p : ℕ} {c₀ sig : ℝ}
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hsig : 0 ≤ sig) (hp : p ≤ N) :
    (((sphereCapGridND d (graphCapScale N a p c₀ sig)).product
        (sphereCapGridND d (graphCapScale N a p c₀ sig))).card:ℝ) ≤
      ((9*(c₀⁻¹+1))^d)^2*(((2:ℝ)^N)^d)^2 := by
  have h := graphCapGrid_card_crude (d:=d) (a:=a) hc₀ hc₀1 hsig hp
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
  calc
    _ ≤ ((9*(c₀⁻¹+1))^d*((2:ℝ)^N)^d)*((9*(c₀⁻¹+1))^d*((2:ℝ)^N)^d) := mul_le_mul h h (by positivity) (by positivity)
    _ = _ := by rw [←sq,mul_pow]

lemma graph_energy_prefactor_crude {N a : ℕ} {v : ℝ} (hv : v ≤ N) :
    (2:ℝ)^((d:ℝ)*(v-a)) ≤ ((2:ℝ)^N)^d := by
  rw [←Real.rpow_natCast (2:ℝ) N, ←Real.rpow_natCast ((2:ℝ)^(N:ℝ)) d, ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have ha : (0:ℝ) ≤ a := by positivity
  nlinarith [show (0:ℝ) ≤ d by positivity]

lemma graph_error_sum_crude {R K L E C Q lam₁ lam₂ T : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hL : 0 ≤ L) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hQ : 0 < Q) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂)
    (hc₁ : lam₁ ≤ R^d) (hc₂ : lam₂ ≤ R^d)
    (hk : K ≤ C*(R^d)^2) (hl : L ≤ (R^d)^2) (he : E ≤ R^d)
    {B : ℝ} (hB : 0 ≤ B) :
    lam₁^2*lam₂^2*E*Q⁻¹*(K*L^2*(B*(R^d)^4*R^(-(T+15*(d:ℝ)))*Q)) ≤ C*B*R^(-T) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hpow : (R^d)^15 * R^(-(T+15*(d:ℝ))) = R^(-T) := by
    rw [←Real.rpow_natCast R d, ←Real.rpow_natCast (R^(d:ℝ)) 15,←Real.rpow_mul hRp.le,←Real.rpow_add hRp]
    congr 1
    ring
  have hcancel : lam₁^2*lam₂^2*E*Q⁻¹*(K*L^2*(B*(R^d)^4*R^(-(T+15*(d:ℝ)))*Q)) =
      (lam₁^2*lam₂^2*E*K*L^2)*B*(R^d)^4*R^(-(T+15*(d:ℝ))) := by
    field_simp
  rw [hcancel]
  have hbody : lam₁^2*lam₂^2*E*K*L^2 ≤ C*(R^d)^11 := by
    calc
      _ ≤ (R^d)^2*(R^d)^2*(R^d)*(C*(R^d)^2)*((R^d)^2)^2 := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (C*(R^d)^11)*B*(R^d)^4*R^(-(T+15*(d:ℝ))) := by gcongr
    _ = C*B*((R^d)^15*R^(-(T+15*(d:ℝ)))) := by ring
    _ = _ := by rw [hpow]
end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer Attempt4FullFar Attempt4Near
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

lemma graph_source_error_sum {N a p : ℕ} {v sig c₀ T E : ℝ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) {B₀ : ℕ} {s₁ s₂ : ℝ} {m₁ m₂ : ℝ → ℝ}
    (hρ : RegularizedProfileData ρ N B₀ s₁ sig m₁)
    (hκ : RegularizedProfileData κ N B₀ s₂ sig m₂)
    (hN : 0 < N) (ha : a ≤ N) (hp : p ≤ N) (hv : v ≤ N)
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hsig : 0 ≤ sig) (hE : 0 ≤ E) (X Y : CellPath d) :
    let R := (2:ℝ)^N
    let lam₁ := R^(-m₁ p)/R^(-m₁ a)
    let lam₂ := R^(-m₂ p)/R^(-m₂ a)
    let Caps := (sphereCapGridND d (graphCapScale N a p c₀ sig)).product
      (sphereCapGridND d (graphCapScale N a p c₀ sig))
    let count := ((graphChildren ρ a p X).card:ℝ)*(graphChildren κ a p Y).card
    lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
      ((Caps.card:ℝ)*count^2*(E*(R^d)^4*R^(-(T+15*(d:ℝ)))*(2:ℝ)^v)) ≤
        ((9*(c₀⁻¹+1))^d)^2*E*R^(-T) := by
  intro R lam₁ lam₂ Caps count
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hl₁ := graph_profile_ratio_crude (d:=d) hR (hρ.profile_le_dim hN ha) (hρ.profile_nonneg hp)
  have hl₂ := graph_profile_ratio_crude (d:=d) hR (hκ.profile_le_dim hN ha) (hκ.profile_nonneg hp)
  have hcount : count ≤ (R^d)^2 := by
    simpa only [count,sq] using mul_le_mul (graphChildren_card_crude ρ hp X)
      (graphChildren_card_crude κ hp Y) (by positivity) (by positivity)
  exact graph_error_sum_crude (d:=d) (T:=T) hR (by positivity : (0:ℝ) ≤ Caps.card)
    (by positivity : 0 ≤ count) (by positivity : (0:ℝ) ≤ (2:ℝ)^((d:ℝ)*(v-a)))
    (by positivity : (0:ℝ) ≤ ((9*(c₀⁻¹+1))^d)^2) (by positivity : (0:ℝ) < (2:ℝ)^v)
    hl₁.1 hl₂.1 hl₁.2 hl₂.2 (graphCapGrid_pair_card_crude hc₀ hc₀1 hsig hp)
    hcount (graph_energy_prefactor_crude (d:=d) hv) hE

noncomputable def graphSourceChildMax
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (a p : ℕ) (v : ℝ)
    (X Y : CellPath d) (M₁ M₂ : ℝ) (Ψ : ℝ → ℝ)
    (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) : ℝ := by
  classical
  exact if h : ((graphChildren ρ a p X).product (graphChildren κ a p Y)).Nonempty then
    graphChildMaxND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) p v Ψ
      (graphChildren ρ a p X) (graphChildren κ a p Y) h
      (fun P z => sourceAngularTransformND ρ (treeCell P) M₁ b z.1 z.2)
      (fun Q z => sourceAngularTransformND κ (treeCell Q) M₂ c z.1 z.2)
  else 0

theorem graph_H_finite_jet_estimate {sig c₀ : ℝ}
    (hsig : 0 < sig) (hc₀ : 0 < c₀) (hcsmall : (d+1:ℝ)*c₀ ≤ 1/2) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (B₀ : ℕ) (s₁ s₂ : ℝ) (m₁ m₂ : ℝ → ℝ),
    RegularizedProfileData ρ N B₀ s₁ sig m₁ → RegularizedProfileData κ N B₀ s₂ sig m₂ →
    ∀ (a p : ℕ) (v L Ctest K B : ℝ) (J i₁ i₂ g₁ g₂ : ℕ)
      (X Y : CellPath d) (Ψ : ℝ → ℝ)
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ),
    a < p → (p:ℝ) ≤ v → v ≤ N →
    (p:ℝ)-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 10*sig*N ≤ v-p →
    a ≤ g₁ → a ≤ g₂ → g₁ < p → g₂ < p →
    (g₁:ℝ) ≤ (a:ℝ)+2*sig*N → (g₂:ℝ) ≤ (a:ℝ)+2*sig*N →
    0 < J → i₁ ≤ J → i₂ ≤ J →
    X ∈ dyadicPaths a → Y ∈ dyadicPaths a → 0 < ρ (treeCell X) → 0 < κ (treeCell Y) →
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 → (∀ r, 0 ≤ Ψ r) →
    (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K → (∀ u, ‖iteratedDeriv m (fun u => (Ψ u:ℂ)) u‖ ≤ K) → 0 ≤ K →
    let R := (2:ℝ)^N
    let A₁ := adjustedProfile (d:=d) m₁ N
    let A₂ := adjustedProfile (d:=d) m₂ N
    let S := R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))
    GraphSymbolJet b m S B → GraphSymbolJet c m S B →
    ImposesParallelTest ρ g₁ p (testWidth N J i₁ p sig) (R^(height A₁ g₁ p+Ctest*sig)) b →
    ImposesParallelTest κ g₂ p (testWidth N J i₂ p sig) (R^(height A₂ g₂ p+Ctest*sig)) c →
    sourceAngularHND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ
      (fun z => sourceAngularTransformND ρ (treeCell X) (R^(-m₁ a)) b z.1 z.2)
      (fun z => sourceAngularTransformND κ (treeCell Y) (R^(-m₂ a)) c z.1 z.2) ≤
    R^(-((A₁ p-A₁ a)+(A₂ p-A₂ a))+min (height A₁ a p) (height A₂ a p)+(Ctest+36*(d:ℝ)+5)*sig)*
      graphSourceChildMax ρ κ a p v X Y (R^(-m₁ p)) (R^(-m₂ p)) Ψ b c + C*K*B^4*R^(-T) := by
  classical
  obtain ⟨m,C,hC,N₁,hdec⟩ := graph_direct_nonedge_decay (d:=d) hsig hc₀ (T+15*(d:ℝ))
  obtain ⟨N₂,hdeg⟩ := source_graph_cap_degrees (d:=d) hsig hc₀
  refine ⟨m,((9*(c₀⁻¹+1))^d)^2*C,by positivity,max 1 (max N₁ N₂),?_⟩
  intro N hN ρ κ B₀ s₁ s₂ m₁ m₂ hρ hκ a p v L Ctest K B J i₁ i₂ g₁ g₂ X Y Ψ b c
    hap hpv hvN hh hL hgap hag₁ hag₂ hg₁ hg₂ hga₁ hga₂ hJ hi₁ hi₂ hX hY hoccX hoccY
    hΨ hsΨ hΨ0 hK hdΨ hK0 R A₁ A₂ S hb hc ht₁ ht₂
  let := hρ.probability
  let := hκ.probability
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hN)
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hpN : p ≤ N := by exact_mod_cast hpv.trans hvN
  have haN := hap.le.trans hpN
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by positivity
  have hc₀1 : c₀ ≤ 1 := by nlinarith [show (0:ℝ) ≤ d by positivity]
  let A := graphChildren ρ a p X
  let Z := graphChildren κ a p Y
  let δ := graphCapScale N a p c₀ sig
  let τ := graphTolerance N p sig
  let Caps := (sphereCapGridND d δ).product (sphereCapGridND d δ)
  let G := fun k : (Fin d → ℤ)×(Fin d → ℤ) =>
    retainedHGraph (eligibleCells ρ a p X (tensorCapND δ k.1) b)
      (eligibleCells κ a p Y (tensorCapND δ k.2) c)
      (sphereCapCenterND δ k.1) (sphereCapCenterND δ k.2) τ
  let η := fun k : (Fin d → ℤ)×(Fin d → ℤ) => fun z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d) =>
    tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2
  let U := fun (P : CellPath d) (z : ℝ × EuclideanSpace ℝ (Fin d)) => sourceAngularTransformND ρ (treeCell P) (R^(-m₁ p)) b z.1 z.2
  let W := fun (Q : CellPath d) (z : ℝ × EuclideanSpace ℝ (Fin d)) => sourceAngularTransformND κ (treeCell Q) (R^(-m₂ p)) c z.1 z.2
  let lam₁ := R^(-m₁ p)/R^(-m₁ a)
  let lam₂ := R^(-m₂ p)/R^(-m₂ a)
  let D := R^(min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig)
  let ε := C*K*B^4*(R^d)^4*R^(-(T+15*(d:ℝ)))*(2:ℝ)^v
  have hAB : (A.product Z).Nonempty := Finset.nonempty_product.mpr
    ⟨graphChildren_nonempty ρ hap.le hX hoccX,graphChildren_nonempty κ hap.le hY hoccY⟩
  have hlabels : (A.card:ℝ)*Z.card ≤ R^((A₁ p-A₁ a)+(A₂ p-A₂ a)+(d:ℝ)*((p:ℝ)-a)/(N:ℝ)+4*(d+1:ℝ)*sig) := by
    have h := graphChildren_pair_profile_card ρ κ hap.le hX hY hRp
      (fun P hP => hρ.graph_child_lower hpN hP) (fun Q hQ => hκ.graph_child_lower hpN hQ)
      (hρ.graph_parent_upper haN hX hoccX) (hκ.graph_parent_upper haN hY hoccY)
    rw [graph_profile_label_exponent (d:=d) m₁ m₂ N a p ((d+1:ℝ)*sig)] at h
    convert h using 1
    congr 1
    dsimp only [A₁,A₂]
    ring
  have hdegree := hdeg N hNN₂ ρ κ A₁ A₂ Ctest J i₁ i₂ a g₁ g₂ p X Y A Z b c
    hag₁ hag₂ hg₁.le hg₂.le hga₁ hga₂ hJ hi₁ hi₂ ht₁ ht₂
  have hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)) :=
    (hΨ.continuous.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ) hsΨ)).comp_div (by positivity)
  have hbounds₁ : ∀ P ∈ A, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)),
      ‖U P (r,w)‖ ≤ |(R^(-m₁ p))⁻¹| * ρ.real (treeCell P)*B := by
    intro P _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
  have hbounds₂ : ∀ Q ∈ Z, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)),
      ‖W Q (r,w)‖ ≤ |(R^(-m₂ p))⁻¹| * κ.real (treeCell Q)*B := by
    intro Q _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
  have hne : ∀ k ∈ Caps, ∀ row ∈ A.product Z, ∀ col ∈ A.product Z, ¬G k row col →
      ‖graphDirectCellTerm ρ κ (R^(-m₁ p)) (R^(-m₂ p)) b c Ψ v δ k.1 k.2 row col‖ ≤ ε := by
    intro k hk row hr col hcol hn
    have hk' := Finset.mem_product.mp hk
    have hd := hdec N hNN₁ a p v L hh hL (sub_nonneg.mpr hpv) ρ κ X Y row col
      (R^(-m₁ p)) (R^(-m₂ p)) (R^d) K B Ψ b c k.1 k.2 hX hY hr hcol
      (by positivity) (by positivity) (by positivity)
      (graphCellLaw_mass_crude ρ hR (hρ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude ρ hR (hρ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude κ hR (hκ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude κ hR (hκ.profile_le_dim hNpos hpN) _)
    rw [←graphCapScale_eq] at hd
    exact hd hk'.1 hk'.2 hΨ hsΨ hK hdΨ hK0 hb hc hn
  have hmain := graphFiniteHND_to_child_max d a p v lam₁ lam₂ hNpos
    (A₁ p-A₁ a) (A₂ p-A₂ a)
    (min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig) (4*(d+1:ℝ)*sig) 1
    (graph_profile_ratio (d:=d) hNpos m₁ a p) (graph_profile_ratio (d:=d) hNpos m₂ a p)
    (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) A Z Caps hAB hlabels G η
    (graph_pair_partition_ae hc₀ hcsmall) U W
    (fun P _ => sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (fun Q _ => sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (fun P => |(R^(-m₁ p))⁻¹| * ρ.real (treeCell P)*B)
    (fun Q => |(R^(-m₂ p))⁻¹| * κ.real (treeCell Q)*B) hbounds₁ hbounds₂ D (by positivity)
    (by simp only [one_mul]; exact le_rfl)
    (fun k hk row _ => ((hdegree k hk).1 row).1)
    (fun k hk col _ => ((hdegree k hk).2 col).1) hiΨ hΨ0
    (fun k _ row _ col _ => by
      simpa only [η,U,W,Complex.ofReal_mul] using
        graph_direct_cell_integrable ρ κ (R^(-m₁ p)) (R^(-m₂ p)) hb hc v hiΨ δ k.1 k.2 row col)
    (show 0 ≤ ε by positivity) (by
      intro k hk row hr col hc hn
      simpa only [graphDirectCellTerm,η,U,W,Complex.ofReal_mul] using hne k hk row hr col hc hn)
  rw [←graph_children_H_split ρ κ hap.le hX hY hb hc (R^(-m₁ a)) (R^(-m₂ a))
    (by positivity : R^(-m₁ p) ≠ 0) (by positivity : R^(-m₂ p) ≠ 0) v Ψ] at hmain
  have hid : graphSourceChildMax ρ κ a p v X Y (R^(-m₁ p)) (R^(-m₂ p)) Ψ b c =
      graphChildMaxND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) p v Ψ A Z hAB U W := by
    unfold graphSourceChildMax
    split_ifs with hx
    · rfl
    · exact (hx hAB).elim
  rw [←hid,one_mul] at hmain
  have hexp : -((A₁ p-A₁ a)+(A₂ p-A₂ a))+
      (min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig)+4*(d+1:ℝ)*sig =
      -((A₁ p-A₁ a)+(A₂ p-A₂ a))+min (height A₁ a p) (height A₂ a p)+(Ctest+36*(d:ℝ)+5)*sig := by ring
  rw [hexp] at hmain
  apply hmain.trans
  apply add_le_add le_rfl
  have herr := graph_source_error_sum (T:=T) ρ κ hρ hκ hNpos haN hpN hvN
    hc₀ hc₀1 hsig.le (by positivity : 0 ≤ C*K*B^4) X Y
  convert herr using 1
  ring
end CurrentFalconer.TreeND
end
end

end OAI
