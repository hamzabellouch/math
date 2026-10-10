import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientAdd

namespace OAI

/-! Multiplying coefficients with small scalar sumsets, with the
rounding cost controlled by an explicit bound for the first coefficient. -/
namespace Falconer
open scoped Pointwise

theorem scalar_coefficient_mul {δ K a b : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (M : ℕ) (haM : |a| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (ha : ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hb : ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (3584*(4*(M : ℝ)+11))*K^8*(scalarCells δ X).card := by
  classical
  have ha' : ((scalarCells δ (X.image (fun x => a*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact ha
  have hb' : ((scalarCells δ (X.image (fun x => b*x)+X)).card : ℝ) ≤
      K*(scalarCells δ X).card := by rw [add_comm]; exact hb
  obtain ⟨Fa,_,hFa,hca⟩ := scalar_ruzsa_covering hδ (X.image fun x => a*x) X hX ha'
  obtain ⟨Fb,_,hFb,hcb⟩ := scalar_ruzsa_covering hδ (X.image fun x => b*x) X hX hb'
  let F := (Fb.image fun f => a*f)+Fa-Fa
  let Z := 3 • X-2 • X
  have hcover : ∀ p ∈ X+X.image (fun x => (a*b)*x),
      ∃ f ∈ F, ∃ z ∈ Z, |p-(f+z)| ≤ (2*M+4 : ℕ)*δ := by
    intro p hp
    obtain ⟨x,hx,t,ht,rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨fb,hfb,u,hu,v,hv,heb⟩ := hcb (b*y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    obtain ⟨f₁,hf₁,u₁,hu₁,v₁,hv₁,he₁⟩ := hca (a*u) (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    obtain ⟨f₂,hf₂,u₂,hu₂,v₂,hv₂,he₂⟩ := hca (a*v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    have hf : a*fb+f₁-f₂ ∈ F := Finset.sub_mem_sub
      (Finset.add_mem_add (Finset.mem_image.mpr ⟨fb,hfb,rfl⟩) hf₁) hf₂
    have h3 : x+u₁+v₂ ∈ 3 • X := by
      have hm := Finset.add_mem_add (Finset.add_mem_add hx hu₁) hv₂
      simpa only [show (3 : ℕ) = 2+1 from rfl,add_nsmul,one_nsmul,two_nsmul] using hm
    have h2 : v₁+u₂ ∈ 2 • X := by simpa only [two_nsmul] using Finset.add_mem_add hv₁ hu₂
    refine ⟨a*fb+f₁-f₂,hf,(x+u₁+v₂)-(v₁+u₂),Finset.sub_mem_sub h3 h2,?_⟩
    have he₀ : |a*(b*y-(fb+(u-v)))| ≤ 2*(M : ℝ)*δ := by
      rw [abs_mul]
      have hh := mul_le_mul haM heb (abs_nonneg _) (Nat.cast_nonneg M)
      nlinarith
    have htri : |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂)))| ≤
        |a*(b*y-(fb+(u-v)))|+|a*u-(f₁+(u₁-v₁))|+|a*v-(f₂+(u₂-v₂))| := by
      calc
        _ ≤ |a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))|+
            |-(a*v-(f₂+(u₂-v₂)))| := by
          simpa only [sub_eq_add_neg] using abs_add_le
            (a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))) (-(a*v-(f₂+(u₂-v₂))))
        _ ≤ _ := by
          rw [abs_neg]
          exact add_le_add (abs_add_le
            (a*(b*y-(fb+(u-v)))) (a*u-(f₁+(u₁-v₁)))) le_rfl
    have heq : x+(a*b)*y-((a*fb+f₁-f₂)+((x+u₁+v₂)-(v₁+u₂))) =
        a*(b*y-(fb+(u-v)))+(a*u-(f₁+(u₁-v₁)))-(a*v-(f₂+(u₂-v₂))) := by ring
    rw [heq]
    push_cast
    linarith
  have hcNat := scalarCells_translate_cover hδ (X+X.image (fun x => (a*b)*x)) F Z (2*M+4) hcover
  have hc : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
      (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := by
    have hh : ((scalarCells δ (X+X.image (fun x => (a*b)*x))).card : ℝ) ≤
        2*(2*((2*(M : ℝ))+4)+3)*(F.card : ℝ)*(scalarCells δ Z).card := by exact_mod_cast hcNat
    convert hh using 1
    ring
  have hFc : (F.card : ℝ) ≤ (Fb.card : ℝ)*(Fa.card : ℝ)*(Fa.card : ℝ) := by
    have hn := (Finset.card_sub_le (s := (Fb.image fun f => a*f)+Fa) (t := Fa)).trans
      (Nat.mul_le_mul_right Fa.card ((Finset.card_add_le (s := Fb.image fun f => a*f) (t := Fa)).trans
        (Nat.mul_le_mul_right Fa.card (Finset.card_image_le (s := Fb)))))
    exact_mod_cast hn
  have hF : (F.card : ℝ) ≤ 8*K^3 := by
    have h1 := mul_le_mul hFb hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ 2*K)
    have h2 := mul_le_mul h1 hFa (Nat.cast_nonneg Fa.card) (by positivity : 0 ≤ (2*K)*(2*K))
    exact hFc.trans (h2.trans_eq (by ring))
  have hZ : ((scalarCells δ Z).card : ℝ) ≤ 7*(2*K)^5*(scalarCells δ X).card := by
    have hz := scalar_pluennecke δ X X hX hdoubling 3 2
    norm_num only at hz
    exact hz
  calc
    _ ≤ (2*(4*(M : ℝ)+11))*(F.card : ℝ)*(scalarCells δ Z).card := hc
    _ ≤ ((2*(4*(M : ℝ)+11))*(8*K^3))*(7*(2*K)^5*(scalarCells δ X).card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by positivity)) hZ
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
