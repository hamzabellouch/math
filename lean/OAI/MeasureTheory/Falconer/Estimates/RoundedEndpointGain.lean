import OAI.MeasureTheory.Falconer.Recursion.ProfileApplicationBudget
import OAI.MeasureTheory.Falconer.Recursion.RoundedProfileGain

namespace OAI

/-! Apply the actual normal/good cell estimates to an inward-rounded profile
partition and close the finite endpoint induction. -/
namespace Falconer
open Set Regularization

theorem rounded_profile_endpoint_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ eg η : ℝ, ∃ Ng : ℕ, 0 < eg ∧ eg ≤ 1 ∧ 0 < η ∧ 0 < Ng ∧
    ∀ m B : ℕ, 0 < m → 0 < B → Even B →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ s t α τ β lam χ r ζ : ℝ, κ ≤ s → s ≤ 1-8*κ → 0 ≤ α → 0 < τ → 0 < β → 0 < lam →
    ∀ J : ℕ, ∀ S : List (ℝ × ℝ),
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       StructuredProfilePieces g τ α (s+κ) 1 S) →
      (let N := m*B;
       let g := fun x => regularizedProfile L (blockLabel L N B f (m+1)) N B (m+1) p ((N:ℝ)*x);
       t-lam ≤ g 1) →
      1-χ ≤ (S.map Prod.snd).sum → s+8*κ ≤ t → lam+2*χ ≤ κ →
      2/(m:ℝ) ≤ τ/2 → 4/(m:ℝ) ≤ α*(τ/2) → 16/((m:ℝ)*τ) ≤ κ/2 →
      (2/(m:ℝ))*(S.length:ℝ) ≤ r → r ≤ κ → S.length ≤ J →
      4*(Ng:ℝ) ≤ τ*(m*B:ℕ) → 4*β ≤ eg*τ/8 → 3*α ≤ eg/4 →
      s+ζ+β ≤ s*(1-χ-r)+η*κ-9*α-13*β*(J:ℝ) →
      (let N := m*B;
       let H : ℝ := (4*(N+2)+11:ℕ);
       let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1);
       let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)));
       (∀ j ≤ 2*J, ∀ A : ℝ,
         profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
       640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
       (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ))) →
      ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
        ((2:ℝ)^((s+ζ)*(m*B:ℕ))) := by
  obtain ⟨eg,η,Ng,heg,heg1,hη,hNg,hcell⟩ := block_cell_power hκ hκ1
  refine ⟨eg,η,Ng,heg,heg1,hη,hNg,?_⟩
  intro m B hm hB hBeven L hL f p Q hQ s t α τ β lam χ r ζ hs hs1 hα hτ hβ hlam J S
    hS hgrowth hcover hgap hweak hmesh herror hslack hround hr hcount hlarge hbeta halpha hgain hbudget
  let N := m*B
  let K := m+1
  let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x)
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have hN : 0 < N := Nat.mul_pos hm hB
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hf : LipschitzWith 2 g := planarProfile_lipschitz hN hL _ B K p
  have hg0 : g 0 = 0 := by simp [g,regularizedProfile_zero]
  obtain ⟨hgeom,hpoly,hcost⟩ := hbudget
  have hrounded := rounded_profile_gain_cells hf hm hτ hα hκ hmesh herror hslack hS
  have hhigh : κ ≤ profileHighLength g (s+2*κ) (S.map (innerProfileCell m)) :=
    rounded_profile_good_length hf hm hτ hκ (hκ.le.trans hs) hmesh
      (by linarith only [hslack,hκ]) hS hg0 hgrowth hcover hgap hweak (hround.trans hr)
  have hord := (rounded_structured_profile_pieces hf hm hτ hα hmesh herror hS).1
  obtain ⟨I,hI,_,hordered⟩ := exists_rounded_block_interval_map hm hB S
    (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1⟩)
    (fun c hc => (half_pos hτ).trans_le (hrounded _ (List.mem_map.mpr ⟨c,hc,rfl⟩)).2.2.1) hord
  let R := S.map I
  let e := fun c : ℕ × ℕ => profileGainExponent g (s+2*κ) s η (9*α) (13*β) N
    (blockProfileCell N B c)
  have hRlen : R.length = S.length := by simp [R]
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B K
  have hW0 : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hW (k : ℕ) : 1 ≤ W k := profileBudgetSequence_one_le hH hG hW0 k
  have hWmono : Monotone W := profileBudgetSequence_monotone hH hG hW0
  have hbase (c : ℕ × ℕ) (hc : c ∈ R) :
      ProfileEndpointBound N B K L f p Q c.1 c.2 s (W (2*R.length)) ((2:ℝ)^(e c)) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    have hi := hI a ha
    have heq : innerProfileCell m a = blockProfileCell N B (I a) :=
      blockProfileCell_eq_of_endpoints hi.2.2.1 hi.2.2.2
    have hh := hrounded (innerProfileCell m a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    rw [heq] at hh
    obtain ⟨n,hn⟩ := exists_half_block_length (m := m) (i := (I a).1) (j := (I a).2) hBeven
    have hcast : ((blockDepth N B (I a).2-blockDepth N B (I a).1:ℕ):ℝ) =
        (blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ) :=
      Nat.cast_sub (blockDepth_antitone N B hi.1.le)
    have hd : τ*(N:ℝ)/2 ≤ (2*n:ℕ) := by
      have hl := hh.2.2.1
      change τ/2 ≤ ((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ))/N at hl
      have hl' := (le_div_iff₀ hNR).mp hl
      rw [← hcast,hn] at hl'
      linarith only [hl']
    have hnlarge : Ng ≤ n+3 := by
      have hnn : (Ng:ℝ) ≤ n := by
        push_cast at hd
        nlinarith only [hd,hlarge]
      have : Ng ≤ n := Nat.cast_le.mp hnn
      omega
    have hscale : (4*β)*(N:ℝ)+(3*α)*
        ((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ)) ≤ eg*((n+3:ℕ):ℝ) := by
      rw [← hcast,hn]
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have h1 := mul_le_mul_of_nonneg_right hbeta hNR.le
      have h2 := mul_le_mul_of_nonneg_left hd heg.le
      have h3 := mul_le_mul_of_nonneg_right halpha (show (0:ℝ) ≤ (2*n:ℕ) by positivity)
      push_cast at h1 h2 h3 ⊢
      nlinarith only [h1,h2,h3,heg]
    have hgeometry := hgeom (2*R.length) (by rw [hRlen]; omega)
      ((3*α)*((blockDepth N B (I a).2:ℝ)-(blockDepth N B (I a).1:ℝ)))
    have hdata : s ≤ intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 ∧
        intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 ≤ 2 ∧
        (∀ x ∈ Icc (blockProfileCell N B (I a)).1
          ((blockProfileCell N B (I a)).1+(blockProfileCell N B (I a)).2),
          -(3*α)*(blockProfileCell N B (I a)).2 ≤ intervalSecantError g
            (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 x) ∧
        (s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 →
          ∀ x ∈ Icc (blockProfileCell N B (I a)).1
            ((blockProfileCell N B (I a)).1+(blockProfileCell N B (I a)).2),
            |intervalSecantError g (blockProfileCell N B (I a)).1 (blockProfileCell N B (I a)).2 x| ≤
              (3*α)*(blockProfileCell N B (I a)).2) := hh.2.2.2
    have hb := hcell n hnlarge s (W (2*R.length)) (3*α) (4*β) β hs hs1
      (hW _) (by positivity) (by positivity) N B K hN L hL f p Q hQ (I a).1 (I a).2
      hi.1.le (by dsimp [K]; omega) hn hdata hgeometry hscale hpoly
    convert hb using 1
    dsimp [e,g]
    ring_nf
  have hcover' : 1-χ-r ≤ ((S.map (innerProfileCell m)).map Prod.snd).sum := by
    have hh := innerProfileCells_length_lower hm S
    linarith only [hh,hcover,hround]
  have hlength : ((S.map (innerProfileCell m)).map Prod.snd).sum ≤ 1 := by
    simpa only [sub_zero] using ordered_interval_length_le (by norm_num : (0:ℝ) ≤ 1) hord
      (fun c hc => ⟨(hrounded c hc).1,(hrounded c hc).2.1,
        (half_pos hτ).le.trans (hrounded c hc).2.2.1⟩)
  have hsum : ((s+ζ)+β)*(N:ℝ) ≤ (R.map e).sum := by
    have hh := profile_gain_exponent_lower (S.map (innerProfileCell m)) g
      hNR.le (hκ.le.trans hs) hη.le (by positivity : 0 ≤ 9*α) (by positivity : 0 ≤ 13*β)
      (κ := χ+r) (h := κ) (J := J) (target := (s+ζ)+β)
      (by convert hcover' using 1; ring) hlength hhigh
      (by simpa only [List.length_map] using (Nat.cast_le.mpr hcount : (S.length:ℝ) ≤ J))
      (by convert hgain using 1; ring)
    have he := rounded_block_gain_sum S I (fun a ha => ⟨(hI a ha).2.2.1,(hI a ha).2.2.2⟩)
      g (s+2*κ) s η (9*α) (13*β) N
    change ((s+ζ)+β)*(N:ℝ) ≤ ((S.map I).map fun c =>
      profileGainExponent g (s+2*κ) s η (9*α) (13*β) N (blockProfileCell N B c)).sum
    rw [he]
    exact hh
  have hcost' : (43264*H^4)^(2*R.length) ≤ (2:ℝ)^(β*(N:ℝ)) := by
    apply le_trans _ hcost
    apply pow_le_pow_right₀
    · have hh : (1:ℝ) ≤ H^4 := one_le_pow₀ hH
      linarith
    · rw [hRlen]
      omega
  exact profileEndpointBound_ordered_power hL f p Q hQ (hκ.le.trans hs) (by linarith) R m 0 hordered
    (by dsimp [K]; omega) e W hW hWmono (fun _ => rfl) hbase
    (target := (s+ζ)*(N:ℝ)) (loss := β*(N:ℝ)) (by nlinarith only [hsum]) hcost'

end Falconer

end OAI
