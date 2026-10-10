import Mathlib
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

def shell (L : ℕ) : Finset Vertex := box L \ interior L

def radialPoint (L : ℕ) (side : Fin 4) (k : ℕ) : Vertex :=
  match side.val with
  | 0 => ((k : ℤ), (L/2 : ℕ))
  | 1 => ((L : ℤ)-(k : ℤ), (L/2 : ℕ))
  | 2 => ((L/2 : ℕ), (k : ℤ))
  | _ => ((L/2 : ℕ), (L : ℤ)-(k : ℤ))

@[simp] lemma mem_shell {L : ℕ} {x : Vertex} :
    x ∈ shell L ↔ x ∈ box L ∧
      (x.1 = 0 ∨ x.1 = (L : ℤ) ∨ x.2 = 0 ∨ x.2 = (L : ℤ)) := by
  simp only [shell, Finset.mem_sdiff, mem_box, interior,
    Finset.mem_product, Finset.mem_Icc]
  omega

lemma latticeDist_nonneg (x y : Vertex) : 0 ≤ latticeDist x y := by
  rw [←intDist_cast]
  exact_mod_cast intDist_nonneg x y

lemma latticeDist_comm (x y : Vertex) : latticeDist x y = latticeDist y x := by
  have hi : intDist x y = intDist y x := by
    rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
    simp only [intDist, abs_eq_max_neg]
    omega
  rw [←intDist_cast, ←intDist_cast, hi]

lemma left_mem_box {m k : ℕ} (hk : k ≤ 2*m) :
    ((k : ℤ), (m : ℤ)) ∈ box (2*m) := by
  simp only [mem_box, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma left_mem_shell_iff {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    ((k : ℤ), (m : ℤ)) ∈ shell (2*m) ↔ k = 0 := by
  simp only [mem_shell, mem_box, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma left_shell_distance {m k : ℕ} (hk : k ≤ m) {b : Vertex}
    (hb : b ∈ shell (2*m)) : (k : ℝ) ≤ latticeDist ((k : ℤ),(m : ℤ)) b := by
  have hi : (k : ℤ) ≤ intDist ((k : ℤ),(m : ℤ)) b := by
    rcases b with ⟨a,c⟩
    simp only [mem_shell, mem_box, Nat.cast_mul, Nat.cast_ofNat] at hb
    simp only [intDist, abs_eq_max_neg]
    omega
  rw [←intDist_cast]
  exact_mod_cast hi

lemma other_face_distance {m : ℕ} {b : Vertex}
    (hb : b ∈ shell (2*m)) (ha : b.1 ≠ 0) :
    (m : ℝ) ≤ latticeDist (0,(m : ℤ)) b := by
  have hi : (m : ℤ) ≤ intDist (0,(m : ℤ)) b := by
    rcases b with ⟨a,c⟩
    simp only [mem_shell, mem_box, Nat.cast_mul, Nat.cast_ofNat] at hb
    simp only [intDist, abs_eq_max_neg]
    omega
  rw [←intDist_cast]
  exact_mod_cast hi

lemma left_compressed_distance {m k l : ℕ} :
    latticeDist ((k : ℤ),(m : ℤ)) (0,(m : ℤ)+(l : ℤ)) = max (k : ℝ) l := by
  have hi : intDist ((k : ℤ),(m : ℤ)) (0,(m : ℤ)+(l : ℤ)) = max (k : ℤ) l := by
    simp only [intDist, abs_eq_max_neg]
    omega
  rw [←intDist_cast, hi]
  simp

lemma left_opposite_distance {m k l : ℕ} :
    latticeDist ((k : ℤ),(m : ℤ)) (0,(m : ℤ)-(l : ℤ)) = k+l := by
  have hi : intDist ((k : ℤ),(m : ℤ)) (0,(m : ℤ)-(l : ℤ)) = (k : ℤ)+l := by
    simp only [intDist, abs_eq_max_neg]
    omega
  rw [←intDist_cast, hi]
  simp

lemma left_radial_distance {m k l : ℕ} :
    latticeDist ((k : ℤ),(m : ℤ)) ((l : ℤ),(m : ℤ)) = |(k : ℝ)-l| := by
  simp [latticeDist]

lemma left_tangential_distance {m k l : ℕ} :
    latticeDist (0,(m : ℤ)+(k : ℤ)) (0,(m : ℤ)+(l : ℤ)) = |(k : ℝ)-l| := by
  simp [latticeDist]

def unitSign (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

lemma abs_unitSign (a : ℝ) : |unitSign a| = 1 := by
  unfold unitSign
  split <;> norm_num

lemma compressed_slack (δ β s₀ l f₁ f : ℝ)
    (_hδ : 0 ≤ δ) (hδβ : β ≤ δ) (hsβ : β ≤ s₀)
    (hl : 1 ≤ l) (hs : s₀ ≤ |f₁|)
    (hf : |f| ≤ (1-δ)*l) (hd : |f-f₁| ≤ (1-δ)*(l-1)) :
    |unitSign f₁-f| ≤ (1-β)*l := by
  have hn := mul_nonneg (sub_nonneg.mpr hδβ) (sub_nonneg.mpr hl)
  rw [abs_le] at hf hd ⊢
  unfold unitSign
  split_ifs with hsign
  · rw [abs_of_nonneg hsign] at hs
    constructor <;> nlinarith
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hs
    constructor <;> nlinarith

lemma far_plus_two_slack (δ₀ β k₀ d : ℝ)
    (hβ : β ≤ δ₀/2) (hk₀ : 4 ≤ δ₀*k₀) (hd : k₀ ≤ d)
    (hδ₀ : 0 ≤ δ₀) : (1-δ₀)*d+2 ≤ (1-β)*d := by
  have hk : 0 ≤ k₀ := by nlinarith
  have hd₀ : 0 ≤ d := hk.trans hd
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ) hd₀,
    mul_le_mul_of_nonneg_left hd hδ₀]

lemma expose_left_compatible {m k : ℕ} (hk : k < m)
    (β : ℝ) (hβ : 0 < β) (hβhalf : β < 1/2)
    (h : Vertex → ℝ) (cx cy : ℝ)
    (hcx : k = 0 → cx = h ((k : ℤ),(m : ℤ)))
    (hc : |cx-cy| = 1)
    (hss : ∀ u ∈ shell (2*m), ∀ v ∈ shell (2*m),
      |h u-h v| ≤ (1-β)*latticeDist u v)
    (hxs : ∀ b ∈ shell (2*m),
      |cx-h b| ≤ (1-β)*latticeDist ((k : ℤ),(m : ℤ)) b)
    (hys : ∀ b ∈ shell (2*m), b ≠ ((k : ℤ),(m : ℤ)) →
      |cy-h b| ≤ (1-β)*latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b) :
    ∃ g : Vertex → ℝ,
      (∀ b ∈ shell (2*m), g b = h b) ∧
      |g ((k : ℤ),(m : ℤ))-g (((k+1 : ℕ) : ℤ),(m : ℤ))| = 1 ∧
      (∀ u ∈ box (2*m), ∀ v ∈ box (2*m), Adj u v →
        s(u,v) ≠ s(((k : ℤ),(m : ℤ)),(((k+1 : ℕ) : ℤ),(m : ℤ))) →
        |g u-g v| ≤ 1-β) := by
  classical
  have hm : 0 < m := by omega
  have hx : ((k : ℤ),(m : ℤ)) ∈ box (2*m) := left_mem_box (by omega)
  have hy : (((k+1 : ℕ) : ℤ),(m : ℤ)) ∈ box (2*m) := left_mem_box (by omega)
  let x : BoxVertex (2*m) := ⟨_,hx⟩
  let y : BoxVertex (2*m) := ⟨_,hy⟩
  let z : BoxVertex (2*m) := ⟨((k : ℤ),(m : ℤ)+1), by
    simp only [mem_box, Nat.cast_mul, Nat.cast_ofNat]
    omega⟩
  have hxy : (boxGraph (2*m)).Adj x y := by
    change Adj ((k : ℤ),(m : ℤ)) (((k+1 : ℕ) : ℤ),(m : ℤ))
    exact Or.inl (by simp)
  have hxz : (boxGraph (2*m)).Adj x z := by
    change Adj ((k : ℤ),(m : ℤ)) ((k : ℤ),(m : ℤ)+1)
    exact Or.inr (Or.inr (Or.inl rfl))
  have hzy : (boxGraph (2*m)).Adj z y := by
    change Adj ((k : ℤ),(m : ℤ)+1) (((k+1 : ℕ) : ℤ),(m : ℤ))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))
  have hbridge := FacetExposure.not_bridge_of_triangle hxz hzy hxy.ne
  obtain ⟨g₀,hg₀,he₀,hs₀⟩ := FacetExposure.expose_shell_edge
    (boxGraph (2*m)) (box_connected (2*m)) x y hxy hbridge β hβ hβhalf
    {b | b.val ∈ shell (2*m)} (fun b => h b.val) cx cy
    (fun hs => hcx ((left_mem_shell_iff hm (by omega)).mp hs))
    (fun hs => False.elim (by
      have := (left_mem_shell_iff hm (Nat.succ_le_of_lt hk)).mp hs
      omega)) hc
    (fun u hu v hv => by rw [box_dist]; exact hss _ hu _ hv)
    (fun b hb _ => by rw [box_dist]; exact hxs _ hb)
    (fun b hb hbne => by
      rw [box_dist]
      exact hys _ hb (fun he => hbne (Subtype.ext he)))
  let g : Vertex → ℝ := fun b => if hb : b ∈ box (2*m) then g₀ ⟨b,hb⟩ else h b
  have hg : ∀ b : BoxVertex (2*m), g b.val = g₀ b := by
    intro b
    dsimp only [g]
    rw [dite_eq_left b.property]
  refine ⟨g,?_,?_,?_⟩
  · intro b hb
    have hbQ := (mem_shell.mp hb).1
    exact (hg ⟨b,hbQ⟩).trans (hg₀ ⟨b,hbQ⟩ hb)
  · change |g x.val-g y.val| = 1
    rw [hg,hg]
    exact he₀
  · intro u hu v hv huv hne
    rw [hg ⟨u,hu⟩,hg ⟨v,hv⟩]
    apply hs₀ ⟨u,hu⟩ ⟨v,hv⟩ huv
    intro he
    apply hne
    exact congrArg (Sym2.map (fun b : BoxVertex (2*m) => b.val)) he

lemma other_face_slack (δ₀ β k₀ m k l d : ℝ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hβδ : β ≤ δ₀/2)
    (hδ₀ : 0 ≤ δ₀) (hk : 0 ≤ k) (hkk₀ : k ≤ k₀)
    (hm : 4*(k₀+2) ≤ δ₀*m) (hl : m ≤ l)
    (hd : l-k-1 ≤ d) : 1+(1-δ₀)*l ≤ (1-β)*d := by
  have hk₀ : 0 ≤ k₀ := hk.trans hkk₀
  have hm₀ : 0 ≤ m := by nlinarith
  have hl₀ : 0 ≤ l := hm₀.trans hl
  have hp := mul_nonneg (sub_nonneg.mpr hβδ) hl₀
  have hq := mul_nonneg hβ₀ (show 0 ≤ k+1 by linarith)
  have hr := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hβ₁)
  have ht := mul_le_mul_of_nonneg_left hl hδ₀
  nlinarith

lemma opposite_slack (δ β k l : ℝ)
    (hδ : δ ≤ 1) (hβ₀ : 0 ≤ β) (hβ : β ≤ δ/2)
    (hk : 0 ≤ k) (_hl : 0 ≤ l) (hkl : 1 ≤ k+l) :
    1+(1-δ)*l ≤ (1-β)*(k+1+l) := by
  have hδ₀ : 0 ≤ δ := by linarith
  have hp := mul_nonneg (show 0 ≤ 1-δ by linarith) hk
  have hq := mul_nonneg (show 0 ≤ δ/2-β by linarith) (show 0 ≤ k+1+l by linarith)
  have hr := mul_nonneg hδ₀ (sub_nonneg.mpr hkl)
  nlinarith

lemma near_left_bounds (h : Vertex → ℝ) {m k k₀ : ℕ} (hk : k < m) (hkk₀ : k < k₀)
    (δ δ₀ s₀ β : ℝ)
    (hδ : 0 < δ) (hδδ₀ : δ ≤ δ₀) (hδ₀ : δ₀ ≤ 1/16)
    (hβ₀ : 0 < β) (hβδ : β ≤ δ/2) (hβs : β ≤ s₀/2)
    (hm : 4*((k₀ : ℝ)+2) ≤ δ₀*(m : ℝ))
    (hnear : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), Adj x y → |h x-h y| ≤ 1-δ)
    (hfar : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), (k₀ : ℝ) ≤ latticeDist x y →
      |h x-h y| ≤ (1-δ₀)*latticeDist x y)
    (hnt : s₀ ≤ |h (0,(m : ℤ)+1)-h (0,(m : ℤ))|) :
    ∀ b ∈ shell (2*m),
      (|h (0,(m : ℤ))-h b| ≤ (1-β)*latticeDist ((k : ℤ),(m : ℤ)) b) ∧
      (b ≠ ((k : ℤ),(m : ℤ)) →
        |h (0,(m : ℤ))+unitSign (h (0,(m : ℤ)+1)-h (0,(m : ℤ)))-h b| ≤
          (1-β)*latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b) := by
  have hmpos : 0 < m := by omega
  have hvmem : (0,(m : ℤ)) ∈ box (2*m) := left_mem_box (k:=0) (by omega)
  have hb₁mem : (0,(m : ℤ)+1) ∈ box (2*m) := by
    simp only [mem_box, Nat.cast_mul, Nat.cast_ofNat]
    omega
  have hδone : δ ≤ 1 := by linarith
  have hβone : β ≤ 1 := by linarith
  have hβδ' : β ≤ δ := by linarith
  have hsβ : β ≤ s₀ := by linarith
  have hδ₀pos : 0 ≤ δ₀ := by linarith
  have hkm : (k₀ : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith
  let τ := unitSign (h (0,(m : ℤ)+1)-h (0,(m : ℤ)))
  have hτ : |τ| = 1 := abs_unitSign _
  have base_bound : ∀ b ∈ box (2*m),
      |h (0,(m : ℤ))-h b| ≤ (1-δ)*latticeDist (0,(m : ℤ)) b :=
    fun b hb => near_global_bound hnear hvmem hb
  have plus_bound : ∀ b : Vertex,
      |h (0,(m : ℤ))+τ-h b| ≤ 1+|h (0,(m : ℤ))-h b| := by
    intro b
    calc
      _ = |τ+(h (0,(m : ℤ))-h b)| := by congr 1; ring
      _ ≤ |τ|+|h (0,(m : ℤ))-h b| := abs_add_le _ _
      _ = _ := by rw [hτ]
  intro b hb
  have hbQ := (mem_shell.mp hb).1
  by_cases hface : b.1 = 0
  · rcases b with ⟨a,c⟩
    change a = 0 at hface
    subst a
    have hc : 0 ≤ c ∧ c ≤ (2*m : ℕ) := (mem_box.mp hbQ).2
    by_cases hcomp : (m : ℤ) < c
    · obtain ⟨l,hcl⟩ : ∃ l : ℕ, c = (m : ℤ)+(l : ℤ) :=
        ⟨(c-(m : ℤ)).toNat, by omega⟩
      have hl : 1 ≤ l := by omega
      have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
      subst c
      have hdistv : latticeDist (0,(m : ℤ)) (0,(m : ℤ)+(l : ℤ)) = (l : ℝ) := by
        simpa only [Nat.cast_zero, max_eq_right (Nat.cast_nonneg l)] using
          (left_compressed_distance (m:=m) (k:=0) (l:=l))
      have hf : |h (0,(m : ℤ)+(l : ℤ))-h (0,(m : ℤ))| ≤ (1-δ)*(l : ℝ) := by
        rw [abs_sub_comm]
        simpa only [hdistv] using base_bound _ hbQ
      have hdist₁ : latticeDist (0,(m : ℤ)+1) (0,(m : ℤ)+(l : ℤ)) = (l : ℝ)-1 := by
        have := left_tangential_distance (m:=m) (k:=1) (l:=l)
        simpa only [Nat.cast_one, abs_of_nonpos (by linarith : (1 : ℝ)-(l : ℝ) ≤ 0),
          neg_sub] using this
      have hd : |(h (0,(m : ℤ)+(l : ℤ))-h (0,(m : ℤ)))-
          (h (0,(m : ℤ)+1)-h (0,(m : ℤ)))| ≤ (1-δ)*((l : ℝ)-1) := by
        have he := near_global_bound hnear hb₁mem hbQ
        rw [hdist₁,abs_sub_comm] at he
        convert he using 1
        congr 1
        ring
      have hcs := compressed_slack δ β s₀ (l : ℝ) _ _ hδ.le hβδ' hsβ hlr hnt hf hd
      constructor
      · rw [left_compressed_distance,abs_sub_comm]
        exact hf.trans ((mul_le_mul_of_nonneg_right (by linarith : 1-δ ≤ 1-β)
          (Nat.cast_nonneg l)).trans (mul_le_mul_of_nonneg_left (le_max_right _ _)
            (by linarith)))
      · intro _
        change |h (0,(m : ℤ))+τ-h (0,(m : ℤ)+(l : ℤ))| ≤ _
        calc
          _ = |τ-(h (0,(m : ℤ)+(l : ℤ))-h (0,(m : ℤ)))| := by congr 1; ring
          _ ≤ (1-β)*(l : ℝ) := hcs
          _ ≤ (1-β)*latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) (0,(m : ℤ)+(l : ℤ)) := by
            rw [left_compressed_distance]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    · obtain ⟨l,hcl⟩ : ∃ l : ℕ, c = (m : ℤ)-(l : ℤ) :=
        ⟨((m : ℤ)-c).toNat, by omega⟩
      subst c
      have hdistv : latticeDist (0,(m : ℤ)) (0,(m : ℤ)-(l : ℤ)) = (l : ℝ) := by
        simpa only [Nat.cast_zero, zero_add] using
          (left_opposite_distance (m:=m) (k:=0) (l:=l))
      have hf : |h (0,(m : ℤ))-h (0,(m : ℤ)-(l : ℤ))| ≤ (1-δ)*(l : ℝ) := by
        simpa only [hdistv] using base_bound _ hbQ
      constructor
      · rw [left_opposite_distance]
        exact hf.trans ((mul_le_mul_of_nonneg_right (by linarith : 1-δ ≤ 1-β)
          (Nat.cast_nonneg l)).trans (mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)] : (l : ℝ) ≤ k+l)
            (by linarith)))
      · intro hne
        have hkl : 1 ≤ k+l := by
          by_contra he
          have hkz : k = 0 := by omega
          have hlz : l = 0 := by omega
          apply hne
          simp [hkz,hlz]
        have hklr : (1 : ℝ) ≤ (k : ℝ)+l := by exact_mod_cast hkl
        change |h (0,(m : ℤ))+τ-h (0,(m : ℤ)-(l : ℤ))| ≤ _
        calc
          _ ≤ 1+|h (0,(m : ℤ))-h (0,(m : ℤ)-(l : ℤ))| := plus_bound _
          _ ≤ 1+(1-δ)*(l : ℝ) := add_le_add (le_refl 1) hf
          _ ≤ (1-β)*((k : ℝ)+1+l) := opposite_slack δ β k l hδone hβ₀.le hβδ
            (Nat.cast_nonneg _) (Nat.cast_nonneg _) hklr
          _ = _ := by rw [left_opposite_distance]; push_cast; ring
  · have hvb := other_face_distance hb hface
    have hf := hfar _ hvmem _ hbQ (hkm.trans hvb)
    have hxv : latticeDist (0,(m : ℤ)) ((k : ℤ),(m : ℤ)) = (k : ℝ) := by
      simpa only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] using
        (left_radial_distance (m:=m) (k:=0) (l:=k))
    have hyv : latticeDist (0,(m : ℤ)) (((k+1 : ℕ) : ℤ),(m : ℤ)) = (k : ℝ)+1 := by
      have he := left_radial_distance (m:=m) (k:=0) (l:=k+1)
      simp only [Nat.cast_zero,zero_sub,abs_neg] at he
      rw [abs_of_nonneg (Nat.cast_nonneg (k+1))] at he
      simpa only [Nat.cast_add,Nat.cast_one] using he
    have hdx := latticeDist_triangle (0,(m : ℤ)) ((k : ℤ),(m : ℤ)) b
    have hdy := latticeDist_triangle (0,(m : ℤ)) (((k+1 : ℕ) : ℤ),(m : ℤ)) b
    rw [hxv] at hdx
    rw [hyv] at hdy
    have hkk₀r : (k : ℝ) ≤ k₀ := by exact_mod_cast Nat.le_of_lt hkk₀
    have boundx := other_face_slack δ₀ β k₀ m k (latticeDist (0,(m : ℤ)) b)
      (latticeDist ((k : ℤ),(m : ℤ)) b) hβ₀.le hβone (by linarith) hδ₀pos
      (Nat.cast_nonneg _) hkk₀r hm hvb (by linarith)
    have boundy := other_face_slack δ₀ β k₀ m k (latticeDist (0,(m : ℤ)) b)
      (latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b) hβ₀.le hβone (by linarith) hδ₀pos
      (Nat.cast_nonneg _) hkk₀r hm hvb (by linarith)
    constructor
    · exact hf.trans ((by linarith : (1-δ₀)*latticeDist (0,(m : ℤ)) b ≤
        1+(1-δ₀)*latticeDist (0,(m : ℤ)) b).trans boundx)
    · intro _
      exact (plus_bound b).trans ((add_le_add (le_refl 1) hf).trans boundy)

lemma far_left_bounds (h : Vertex → ℝ) {m k k₀ : ℕ}
    (hk : k < m) (hkk₀ : k₀ ≤ k)
    (δ δ₀ β : ℝ) (hδ : 0 < δ) (hδδ₀ : δ ≤ δ₀)
    (hβδ : β ≤ δ/2) (hk₀ : 4 ≤ δ₀*(k₀ : ℝ))
    (hnear : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), Adj x y → |h x-h y| ≤ 1-δ)
    (hfar : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), (k₀ : ℝ) ≤ latticeDist x y →
      |h x-h y| ≤ (1-δ₀)*latticeDist x y) :
    ∀ b ∈ shell (2*m),
      (|h ((k : ℤ),(m : ℤ))-h b| ≤ (1-β)*latticeDist ((k : ℤ),(m : ℤ)) b) ∧
      (|h ((k : ℤ),(m : ℤ))+1-h b| ≤
        (1-β)*latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b) := by
  have hx : ((k : ℤ),(m : ℤ)) ∈ box (2*m) := left_mem_box (by omega)
  have hy : (((k+1 : ℕ) : ℤ),(m : ℤ)) ∈ box (2*m) := left_mem_box (by omega)
  have hxy : Adj ((k : ℤ),(m : ℤ)) (((k+1 : ℕ) : ℤ),(m : ℤ)) := Or.inl (by simp)
  have hnearxy := hnear _ hx _ hy hxy
  have hchange : |h ((k : ℤ),(m : ℤ))+1-h (((k+1 : ℕ) : ℤ),(m : ℤ))| ≤ 2 := by
    calc
      _ = |(h ((k : ℤ),(m : ℤ))-h (((k+1 : ℕ) : ℤ),(m : ℤ)))+1| := by congr 1; ring
      _ ≤ |h ((k : ℤ),(m : ℤ))-h (((k+1 : ℕ) : ℤ),(m : ℤ))|+|1| := abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; linarith
  intro b hb
  have hbQ := (mem_shell.mp hb).1
  have hrx : (k₀ : ℝ) ≤ latticeDist ((k : ℤ),(m : ℤ)) b :=
    ((by exact_mod_cast hkk₀) : (k₀ : ℝ) ≤ k).trans (left_shell_distance (Nat.le_of_lt hk) hb)
  have hry : (k₀ : ℝ) ≤ latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b :=
    ((by exact_mod_cast (show k₀ ≤ k+1 by omega)) : (k₀ : ℝ) ≤ (k+1 : ℕ)).trans
      (left_shell_distance (Nat.succ_le_of_lt hk) hb)
  have hfx := hfar _ hx _ hbQ hrx
  have hfy := hfar _ hy _ hbQ hry
  have hsx := far_plus_two_slack δ₀ β k₀ (latticeDist ((k : ℤ),(m : ℤ)) b)
    (by linarith) hk₀ hrx (by linarith)
  have hsy := far_plus_two_slack δ₀ β k₀ (latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b)
    (by linarith) hk₀ hry (by linarith)
  constructor
  · linarith
  · calc
      _ ≤ |h ((k : ℤ),(m : ℤ))+1-h (((k+1 : ℕ) : ℤ),(m : ℤ))|+
          |h (((k+1 : ℕ) : ℤ),(m : ℤ))-h b| := abs_sub_le _ _ _
      _ ≤ 2+(1-δ₀)*latticeDist (((k+1 : ℕ) : ℤ),(m : ℤ)) b := add_le_add hchange hfy
      _ ≤ _ := by linarith

lemma expose_left_radial (h : Vertex → ℝ) {m k k₀ : ℕ} (hk : k < m)
    (δ δ₀ s₀ β : ℝ)
    (hδ : 0 < δ) (hδδ₀ : δ ≤ δ₀) (hδ₀ : δ₀ ≤ 1/16)
    (hk₀ : 4 ≤ δ₀*(k₀ : ℝ))
    (hβ₀ : 0 < β) (hβδ : β ≤ δ/2) (hβs : β ≤ s₀/2)
    (hm : 4*((k₀ : ℝ)+2) ≤ δ₀*(m : ℝ))
    (hnear : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), Adj x y → |h x-h y| ≤ 1-δ)
    (hfar : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), (k₀ : ℝ) ≤ latticeDist x y →
      |h x-h y| ≤ (1-δ₀)*latticeDist x y)
    (hnt : s₀ ≤ |h (0,(m : ℤ)+1)-h (0,(m : ℤ))|) :
    ∃ g : Vertex → ℝ,
      (∀ b ∈ shell (2*m), g b = h b) ∧
      |g ((k : ℤ),(m : ℤ))-g (((k+1 : ℕ) : ℤ),(m : ℤ))| = 1 ∧
      (∀ u ∈ box (2*m), ∀ v ∈ box (2*m), Adj u v →
        s(u,v) ≠ s(((k : ℤ),(m : ℤ)),(((k+1 : ℕ) : ℤ),(m : ℤ))) →
        |g u-g v| ≤ 1-β) := by
  have hβhalf : β < 1/2 := by linarith
  have hss : ∀ u ∈ shell (2*m), ∀ v ∈ shell (2*m),
      |h u-h v| ≤ (1-β)*latticeDist u v := by
    intro u hu v hv
    exact (near_global_bound hnear (mem_shell.mp hu).1 (mem_shell.mp hv).1).trans
      (mul_le_mul_of_nonneg_right (by linarith) (latticeDist_nonneg u v))
  by_cases hkk₀ : k < k₀
  · have hb := near_left_bounds h hk hkk₀ δ δ₀ s₀ β hδ hδδ₀ hδ₀ hβ₀ hβδ hβs hm
      hnear hfar hnt
    apply expose_left_compatible hk β hβ₀ hβhalf h
      (h (0,(m : ℤ))) (h (0,(m : ℤ))+unitSign (h (0,(m : ℤ)+1)-h (0,(m : ℤ))))
      (by intro hkz; simp [hkz]) _ hss (fun b hbs => (hb b hbs).1) (fun b hbs => (hb b hbs).2)
    simpa only [sub_add_cancel_left,abs_neg] using abs_unitSign (h (0,(m : ℤ)+1)-h (0,(m : ℤ)))
  · have hb := far_left_bounds h hk (Nat.le_of_not_gt hkk₀) δ δ₀ β hδ hδδ₀ hβδ hk₀ hnear hfar
    exact expose_left_compatible hk β hβ₀ hβhalf h
      (h ((k : ℤ),(m : ℤ))) (h ((k : ℤ),(m : ℤ))+1) (fun _ => rfl)
      (by simp) hss (fun b hbs => (hb b hbs).1) (fun b hbs _ => (hb b hbs).2)

def boxSymmetry (L : ℕ) (side : Fin 4) (x : Vertex) : Vertex :=
  match side.val with
  | 0 => x
  | 1 => ((L : ℤ)-x.1,(L : ℤ)-x.2)
  | 2 => (x.2,x.1)
  | _ => ((L : ℤ)-x.2,(L : ℤ)-x.1)

lemma boxSymmetry_involutive (L : ℕ) (side : Fin 4) :
    Function.Involutive (boxSymmetry L side) := by
  intro x
  rcases x with ⟨a,b⟩
  fin_cases side <;> simp [boxSymmetry]

lemma boxSymmetry_injective (L : ℕ) (side : Fin 4) :
    Function.Injective (boxSymmetry L side) :=
  (boxSymmetry_involutive L side).injective

lemma boxSymmetry_mem_box (L : ℕ) (side : Fin 4) (x : Vertex) :
    boxSymmetry L side x ∈ box L ↔ x ∈ box L := by
  rcases x with ⟨a,b⟩
  fin_cases side <;> simp only [boxSymmetry,mem_box] <;> omega

lemma boxSymmetry_mem_shell (L : ℕ) (side : Fin 4) (x : Vertex) :
    boxSymmetry L side x ∈ shell L ↔ x ∈ shell L := by
  rcases x with ⟨a,b⟩
  fin_cases side <;> simp only [boxSymmetry,mem_shell,mem_box] <;> omega

lemma boxSymmetry_adj (L : ℕ) (side : Fin 4) {x y : Vertex} (hxy : Adj x y) :
    Adj (boxSymmetry L side x) (boxSymmetry L side y) := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  fin_cases side <;> simp only [boxSymmetry,Adj,Prod.mk.injEq] at * <;> omega

lemma boxSymmetry_distance (L : ℕ) (side : Fin 4) (x y : Vertex) :
    latticeDist (boxSymmetry L side x) (boxSymmetry L side y) = latticeDist x y := by
  rw [←intDist_cast,←intDist_cast]
  have hi : intDist (boxSymmetry L side x) (boxSymmetry L side y) = intDist x y := by
    rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
    fin_cases side <;> simp only [boxSymmetry,intDist,abs_eq_max_neg] <;> omega
  rw [hi]

lemma boxSymmetry_left_radial (m k : ℕ) (side : Fin 4) :
    boxSymmetry (2*m) side ((k : ℤ),(m : ℤ)) = radialPoint (2*m) side k := by
  fin_cases side <;> simp [boxSymmetry,radialPoint] <;> omega

lemma boxSymmetry_left_center (m : ℕ) (side : Fin 4) :
    boxSymmetry (2*m) side (0,(m : ℤ)) = faceCenter (2*m) side := by
  fin_cases side <;> simp [boxSymmetry,faceCenter] <;> omega

lemma boxSymmetry_left_neighbor (m : ℕ) (side : Fin 4) :
    boxSymmetry (2*m) side (0,(m : ℤ)+1) = compressedNeighbor (2*m) side := by
  fin_cases side <;> simp [boxSymmetry,compressedNeighbor] <;> omega

theorem triangular_radial_exposure
    (δ δ₀ s₀ : ℝ) (k₀ L : ℕ)
    (hδ : 0 < δ) (hδδ₀ : δ ≤ δ₀) (hδ₀ : δ₀ ≤ 1/16)
    (hk₀ : 4/δ₀ ≤ (k₀ : ℝ)) (hs₀ : 0 < s₀)
    (hLeven : Even L) (hL : 8*((k₀ : ℝ)+2)/δ₀ ≤ (L : ℝ)) :
    ∃ β : ℝ, 0 < β ∧ β < 1/4 ∧ β ≤ δ/2 ∧ β ≤ s₀/2 ∧
      ∀ h : Vertex → ℝ, ConvexGood L k₀ δ δ₀ s₀ h →
        ∀ side : Fin 4, ∀ k : ℕ, k < L/2 →
          ∃ g : Vertex → ℝ,
            (∀ b ∈ shell L, g b = h b) ∧
            |g (radialPoint L side k)-g (radialPoint L side (k+1))| = 1 ∧
            (∀ x ∈ box L, ∀ y ∈ box L, Adj x y →
              s(x,y) ≠ s(radialPoint L side k, radialPoint L side (k+1)) →
                |g x-g y| ≤ 1-β) := by
  obtain ⟨m,hm⟩ := hLeven
  have hLeq : L = 2*m := by omega
  clear hm
  subst L
  let β := min (δ/4) (s₀/4)
  have hβ₀ : 0 < β := lt_min (by linarith) (by linarith)
  have hβδ : β ≤ δ/2 := (min_le_left _ _).trans (by linarith)
  have hβs : β ≤ s₀/2 := (min_le_right _ _).trans (by linarith)
  have hβ₁ : β < 1/4 := by linarith
  have hδ₀pos : 0 < δ₀ := hδ.trans_le hδδ₀
  have hk₀' : 4 ≤ δ₀*(k₀ : ℝ) := by
    have := (div_le_iff₀ hδ₀pos).mp hk₀
    nlinarith
  have hm' : 4*((k₀ : ℝ)+2) ≤ δ₀*(m : ℝ) := by
    have he := (div_le_iff₀ hδ₀pos).mp hL
    push_cast at he
    nlinarith
  refine ⟨β,hβ₀,hβ₁,hβδ,hβs,?_⟩
  intro h hh side k hk
  have hk' : k < m := by simpa using hk
  rcases hh with ⟨hnear,hfar,hnt⟩
  let T := boxSymmetry (2*m) side
  have hnear' : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), Adj x y →
      |(h ∘ T) x-(h ∘ T) y| ≤ 1-δ := by
    intro x hx y hy hxy
    exact hnear _ ((boxSymmetry_mem_box _ _ _).mpr hx)
      _ ((boxSymmetry_mem_box _ _ _).mpr hy) (boxSymmetry_adj _ _ hxy)
  have hfar' : ∀ x ∈ box (2*m), ∀ y ∈ box (2*m), (k₀ : ℝ) ≤ latticeDist x y →
      |(h ∘ T) x-(h ∘ T) y| ≤ (1-δ₀)*latticeDist x y := by
    intro x hx y hy hxy
    have he := hfar (T x) ((boxSymmetry_mem_box _ _ _).mpr hx)
      (T y) ((boxSymmetry_mem_box _ _ _).mpr hy)
      (by simpa only [T,boxSymmetry_distance] using hxy)
    simpa only [Function.comp_apply,T,boxSymmetry_distance] using he
  have hnt' : s₀ ≤ |(h ∘ T) (0,(m : ℤ)+1)-(h ∘ T) (0,(m : ℤ))| := by
    simpa only [Function.comp_apply,T,boxSymmetry_left_center,boxSymmetry_left_neighbor]
      using hnt side
  obtain ⟨g₀,hg₀,he₀,hs₀⟩ := expose_left_radial (h ∘ T) hk' δ δ₀ s₀ β
    hδ hδδ₀ hδ₀ hk₀' hβ₀ hβδ hβs hm' hnear' hfar' hnt'
  have hinv : ∀ x, T (T x) = x := boxSymmetry_involutive _ _
  have hpoint : ∀ j, T (radialPoint (2*m) side j) = ((j : ℤ),(m : ℤ)) := by
    intro j
    rw [←boxSymmetry_left_radial]
    exact hinv _
  refine ⟨g₀ ∘ T,?_,?_,?_⟩
  · intro b hb
    have he := hg₀ (T b) ((boxSymmetry_mem_shell _ _ _).mpr hb)
    simpa only [Function.comp_apply,hinv] using he
  · simpa only [Function.comp_apply,hpoint] using he₀
  · intro x hx y hy hxy hne
    apply hs₀ (T x) ((boxSymmetry_mem_box _ _ _).mpr hx)
      (T y) ((boxSymmetry_mem_box _ _ _).mpr hy) (boxSymmetry_adj _ _ hxy)
    intro he
    apply hne
    have he' := congrArg (Sym2.map T) he
    simpa only [Sym2.map_mk,hinv,T,boxSymmetry_left_radial] using he'

end TriangularLipschitz

end

end OAI
