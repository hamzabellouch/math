import OAI.NumberTheory.TotientAsymptotic.TwoCoordinateGrid
import OAI.NumberTheory.TotientAsymptotic.TwoBandUnionCount

namespace OAI

/-! The two-coordinate instance of Ford Lemma 4.2, before absorbing errors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def coordinateCutoffPairs (S K : ℕ) (T : ℝ) : Finset (ℕ×ℕ) :=
  (((Finset.Icc 2 K).product (Finset.Icc 2 K)).image
    (fun q : ℕ×ℕ => (loglogCutoff q.1,loglogCutoff q.2))).filter
      (fun q => S ≤ q.2 ∧ q.2 ≤ q.1 ∧ T ≤ a 1*B q.1+a 2*B q.2)

lemma coordinateCutoffPairs_card (S K : ℕ) (T : ℝ) :
    (coordinateCutoffPairs S K T).card ≤ (K+1)^2 := by
  have hI : (Finset.Icc 2 K).card ≤ K+1 := by simp; omega
  calc
    _ ≤ (((Finset.Icc 2 K).product (Finset.Icc 2 K)).image
        (fun q : ℕ×ℕ => (loglogCutoff q.1,loglogCutoff q.2))).card := Finset.card_filter_le _ _
    _ ≤ ((Finset.Icc 2 K).product (Finset.Icc 2 K)).card := Finset.card_image_le
    _ = (Finset.Icc 2 K).card*(Finset.Icc 2 K).card := Finset.card_product _ _
    _ ≤ (K+1)^2 := by nlinarith

lemma coordinateCutoffPairs_data {S K : ℕ} {T : ℝ} {q : ℕ×ℕ}
    (hq : q ∈ coordinateCutoffPairs S K T) :
    S ≤ q.2 ∧ q.2 ≤ q.1 ∧ B q.1 ≤ K ∧ Real.log q.1 ≤ Real.exp K ∧
      T ≤ a 1*B q.1+a 2*B q.2 := by
  obtain ⟨hq,hS,horder,hT⟩ := Finset.mem_filter.mp hq
  obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  have hi' := Finset.mem_Icc.mp hi
  have hb := loglogCutoff_bounds (by exact_mod_cast hi'.1 : (2:ℝ) ≤ ij.1)
  exact ⟨hS,horder,hb.2.2.1.trans (by exact_mod_cast hi'.2),
    hb.2.2.2.trans (Real.exp_le_exp.mpr (by exact_mod_cast hi'.2)),hT⟩

/-- Every counted value has some violating preimage. Its regularity controls
all preimages, allowing the actual witness to supply the grid cell. -/
theorem two_coordinate_violation_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (X K L : ℕ) (ω : ℝ),4 ≤ X → 12 ≤ B X → 0 ≤ ω → 2 ≤ L → L ≤ K →
    (L:ℝ)+2 ≤ B X/2 → (K:ℝ) ≤ B X+2 →
    Real.exp K ≤ Real.log X/(20*B X) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,v ≤ X ∧ CountingRegular (loglogCutoff L) X v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X < a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2) →
    (Q.card:ℝ) ≤ C*X*(K+1:ℕ)^2*
      Real.exp (-(1+ω)*B X+(3/2:ℝ)*(B X+5-K)+4*B (loglogCutoff L)+5*D+
        8*Real.sqrt (B (loglogCutoff L)*K)) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := two_band_union_count
  refine ⟨C,D,hC,hD,?_⟩
  intro X K L ω hX hBX hω hL hLK hLB hKB hcut Q hQ
  let S := loglogCutoff L
  let T := (1+ω)*B X-(3/2:ℝ)*(B X+5-K)
  let P := coordinateCutoffPairs S K T
  have hS := loglogCutoff_bounds (by exact_mod_cast hL : (2:ℝ) ≤ L)
  have hBS : 0 ≤ B S := by
    have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
    linarith only [hS.2.1,hLR]
  have hpdata (q : ℕ×ℕ) (hq : q ∈ P) : S ≤ q.2 ∧ q.2 ≤ q.1 ∧ B q.1 ≤ (K:ℝ) ∧
      Real.log q.1 ≤ Real.log X/(20*B X) ∧ T ≤ a 1*B q.1+a 2*B q.2 := by
    obtain ⟨h1,h2,h3,h4,h5⟩ := coordinateCutoffPairs_data hq
    exact ⟨h1,h2,h3,h4.trans hcut,h5⟩
  have hcoverage (v : ℕ) (hv : v ∈ Q) : v ≤ X ∧ CountingRegular S X v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧ 3 ≤ n.primeFactorsList.length ∧
        ∃ q ∈ P,q.1 < fordPrime n 1 ∧ q.2 < fordPrime n 2 := by
    obtain ⟨hvX,hreg,n,hn,hφ,hbad⟩ := hQ v hv
    have hφX : (n.totient:ℝ) ≤ X := by rw [hφ]; exact_mod_cast hvX
    have hg := two_coordinate_grid (by exact_mod_cast hX : (4:ℝ) ≤ X) hBX hω hn hφX hbad
      (hL.trans hLK) hKB hLK hLB
    dsimp only at hg
    obtain ⟨hlen,hi2,hiK,hj2,hjK,hSj,hji,hip,hjp,hBi,hlogi,hT⟩ := hg
    let i := cappedLoglogIndex K (B (fordPrime n 1))
    let j := cappedLoglogIndex K (B (fordPrime n 2))
    refine ⟨hvX,hreg,n,hn,hφ,hlen,(loglogCutoff i,loglogCutoff j),?_,hip,hjp⟩
    refine Finset.mem_filter.mpr ⟨?_,hSj,hji,hT⟩
    apply Finset.mem_image.mpr
    exact ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hi2,hiK⟩,
      Finset.mem_Icc.mpr ⟨hj2,hjK⟩⟩,rfl⟩
  have hb := hbound S X hS.1 hBS (by linarith) K T P hpdata Q hcoverage
  have hcard : (P.card:ℝ) ≤ ((K+1:ℕ)^2:ℝ) := by exact_mod_cast coordinateCutoffPairs_card S K T
  calc
    _ ≤ C*X*P.card*Real.exp (-T+4*B S+5*D+8*Real.sqrt (B S*K)) := hb
    _ ≤ C*X*((K+1:ℕ)^2:ℝ)*Real.exp (-T+4*B S+5*D+8*Real.sqrt (B S*K)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = _ := by dsimp [T,S]; congr 1; congr 1; ring

end TotientAsymptotic

end

end OAI
