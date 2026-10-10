import OAI.MeasureTheory.Falconer.Estimates.ScalarPluennecke
import OAI.MeasureTheory.Falconer.Geometry.ScalarRuzsaCovering
import OAI.MeasureTheory.Falconer.Geometry.ScalarCoverCount

namespace OAI

/-! Adding two coefficients with small scalar sumsets preserves a
polynomial covering bound. This is an algebraic step in sum-product. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_add {δ K a b : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hb : ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a+b)*x))).card : ℝ) ≤
      19712*K^7*(scalarCells δ X).card := by
  classical
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hb' : ((scalarCells δ (X.image (fun x => b*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact hb
  obtain ⟨Fa,_,hFa,hca⟩ := scalar_ruzsa_covering hδ (X.image fun x => a*x) X hX ha'
  obtain ⟨Fb,_,hFb,hcb⟩ := scalar_ruzsa_covering hδ (X.image fun x => b*x) X hX hb'
  let F := Fa+Fb
  let Z := 3 • X-2 • X
  have hcover : ∀ p ∈ X+X.image (fun x => (a+b)*x),
      ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ (4 : ℕ)*δ := by
    intro p hp
    obtain ⟨x,hx,t,ht,rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨fa,hfa,u,hu,v,hv,hea⟩ := hca (a*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    obtain ⟨fb,hfb,w,hw,z,hz,heb⟩ := hcb (b*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    have h3 : x+u+w ∈ 3 • X := by
      have hmem := Finset.add_mem_add (Finset.add_mem_add hx hu) hw
      simpa only [show (3 : ℕ) = 2+1 from rfl,add_nsmul,one_nsmul,two_nsmul] using hmem
    have h2 : v+z ∈ 2 • X := by simpa only [two_nsmul] using Finset.add_mem_add hv hz
    refine ⟨fa+fb,Finset.add_mem_add hfa hfb,(x+u+w)-(v+z),Finset.sub_mem_sub h3 h2,?_⟩
    calc
      |x+(a+b)*y-(fa+fb+((x+u+w)-(v+z)))| =
          |(a*y-(fa+(u-v)))+(b*y-(fb+(w-z)))| := by congr 1; ring
      _ ≤ |a*y-(fa+(u-v))|+|b*y-(fb+(w-z))| := abs_add_le _ _
      _ ≤ (4 : ℕ)*δ := by norm_num; linarith
  have hcNat := scalarCells_translate_cover hδ (X+X.image (fun x => (a+b)*x)) F Z 4 hcover
  have hc : ((scalarCells δ (X+X.image (fun x => (a+b)*x))).card : ℝ) ≤
      22*(F.card : ℝ)*(scalarCells δ Z).card := by exact_mod_cast hcNat
  have hFc : (F.card : ℝ) ≤ (Fa.card : ℝ)*(Fb.card : ℝ) := by exact_mod_cast Finset.card_add_le (s := Fa) (t := Fb)
  have hF : (F.card : ℝ) ≤ 4*K^2 := by
    have hh := hFc.trans (mul_le_mul hFa hFb (Nat.cast_nonneg _) (by positivity))
    nlinarith
  have hZ : ((scalarCells δ Z).card : ℝ) ≤ 7*(2*K)^5*(scalarCells δ X).card := by
    have hz := scalar_pluennecke δ X X hX hdoubling 3 2
    norm_num only at hz
    exact hz
  calc
    _ ≤ 22*(F.card : ℝ)*(scalarCells δ Z).card := hc
    _ ≤ (22*(4*K^2))*(7*(2*K)^5*(scalarCells δ X).card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hZ
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
