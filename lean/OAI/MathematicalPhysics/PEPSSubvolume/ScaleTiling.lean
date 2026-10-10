import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.SquareRecurrence

namespace OAI

/-! Residue-grid partitions and all-scale square estimates. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open RectangleContours
variable {L : ℕ}

def rect (lo₁ lo₂ : ℤ) (w h : ℕ) : Finset (Vertex L) :=
  rectangle lo₁ (lo₁+w-1) lo₂ (lo₂+h-1) 0

lemma mem_rect (lo₁ lo₂ : ℤ) (w h : ℕ) (v : Vertex L) :
    v∈rect lo₁ lo₂ w h ↔
      (0≤(v.1.val:ℤ)-lo₁ ∧ (v.1.val:ℤ)-lo₁<w) ∧
      (0≤(v.2.val:ℤ)-lo₂ ∧ (v.2.val:ℤ)-lo₂<h) := by
  simp only [rect,mem_rectangle,Nat.cast_zero,sub_zero,add_zero]
  omega

lemma rect_card_le (lo₁ lo₂ : ℤ) (w h : ℕ) :
    (rect (L:=L) lo₁ lo₂ w h).card≤w*h := by
  let f : {v : Vertex L // v∈rect lo₁ lo₂ w h} → Fin w × Fin h := fun v =>
    (⟨((v.val.1.val:ℤ)-lo₁).toNat,by
      have hh := (mem_rect lo₁ lo₂ w h v.val).mp v.property
      omega⟩,
     ⟨((v.val.2.val:ℤ)-lo₂).toNat,by
      have hh := (mem_rect lo₁ lo₂ w h v.val).mp v.property
      omega⟩)
  have hf : Function.Injective f := by
    intro v u he
    have hv := (mem_rect lo₁ lo₂ w h v.val).mp v.property
    have hu := (mem_rect lo₁ lo₂ w h u.val).mp u.property
    have h1 := congrArg (fun z : Fin w × Fin h => z.1.val) he
    have h2 := congrArg (fun z : Fin w × Fin h => z.2.val) he
    dsimp only [f] at h1 h2
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using hh

lemma box_eq_rect (lo₁ lo₂ : ℤ) (M r : ℕ) :
    box (L:=L) lo₁ lo₂ M r=rect lo₁ lo₂ (M*r) (M*r) := by
  simp only [box,rect,Nat.cast_mul]

lemma box_mono (lo₁ lo₂ : ℤ) {n m : ℕ} (hnm : n ≤ m) :
    box (L:=L) lo₁ lo₂ 1 n ⊆ box lo₁ lo₂ 1 m := by
  intro v hv
  rw [mem_box] at hv ⊢
  have hh : (n:ℤ)≤ m := by exact_mod_cast hnm
  simpa only [Nat.cast_one,one_mul] using
    And.intro (And.intro hv.1.1 (lt_of_lt_of_le (by simpa using hv.1.2) hh))
      (And.intro hv.2.1 (lt_of_lt_of_le (by simpa using hv.2.2) hh))

lemma box_remainder_card (lo₁ lo₂ : ℤ) (n r : ℕ) (hr : 0<r) :
    (box (L:=L) lo₁ lo₂ 1 n\box lo₁ lo₂ (n/r) r).card≤2*n*r := by
  classical
  let c := n/r*r
  let S := rect (L:=L) (lo₁+c) lo₂ (n-c) n
  let T := rect (L:=L) lo₁ (lo₂+c) n (n-c)
  have hc : c≤n := Nat.div_mul_le_self _ _
  have hrem : n-c<r := by
    have hh := Nat.mod_add_div n r
    rw [Nat.mul_comm r (n/r)] at hh
    have hl := Nat.mod_lt n hr
    dsimp only [c]
    omega
  have hsub : box (L:=L) lo₁ lo₂ 1 n\box lo₁ lo₂ (n/r) r ⊆ S∪T := by
    intro v hv
    obtain ⟨hv,hn⟩ := Finset.mem_sdiff.mp hv
    rw [mem_box] at hv hn
    simp only [Nat.cast_one,one_mul] at hv
    have he : ((n/r:ℕ):ℤ)*(r:ℤ)=(c:ℤ) := by simp only [c,Nat.cast_mul]
    rw [he] at hn
    have hcn : (c:ℤ)≤n := by exact_mod_cast hc
    have hd : ((n-c:ℕ):ℤ)=(n:ℤ)-c := Nat.cast_sub hc
    by_cases h1 : (v.1.val:ℤ)-lo₁<(c:ℤ)
    · apply Finset.mem_union_right
      change v∈rect lo₁ (lo₂+c) n (n-c)
      rw [mem_rect,hd]
      omega
    · apply Finset.mem_union_left
      change v∈rect (lo₁+c) lo₂ (n-c) n
      rw [mem_rect,hd]
      omega
  have h1 := rect_card_le (L:=L) (lo₁+c) lo₂ (n-c) n
  have h2 := rect_card_le (L:=L) lo₁ (lo₂+c) n (n-c)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le S T)
  have hmul := Nat.mul_le_mul_left n (Nat.le_of_lt hrem)
  dsimp only [S,T] at hh
  nlinarith only [hh,h1,h2,hmul]

end PolynomialPEPS.Subvolume.RectangleTiling

namespace PolynomialPEPS.Subvolume.RectangleTiling
open scoped BigOperators
open PolynomialPEPS.Subvolume.HarmonicWeights PolynomialPEPS.Subvolume.GeometricLower
open PolynomialPEPS.Subvolume.RectangleContours
variable {L q : ℕ}

theorem entropy_square_tiling_bound (hq : 0<q) (Ω : State L q) (hΩ : ‖Ω‖=1)
    (lo₁ lo₂ : ℤ) (n r : ℕ) (hr : 0<r) (F : ℝ)
    (hF : ∀ i : Index (n/r), vonNeumannEntropy Ω (tile lo₁ lo₂ r i)≤F) :
    vonNeumannEntropy Ω (box lo₁ lo₂ 1 n) ≤
      ((n/r:ℕ):ℝ)^2*F+2*(n:ℝ)*(r:ℝ)*Real.log q := by
  classical
  let E := box (L:=L) lo₁ lo₂ 1 n
  let B := box (L:=L) lo₁ lo₂ (n/r) r
  have hBE : B ⊆ E := by
    dsimp only [B,E]
    rw [box_mul]
    exact box_mono lo₁ lo₂ (Nat.div_mul_le_self n r)
  have hdiff : E\(E\B)=B := by
    ext v
    simp only [Finset.mem_sdiff]
    constructor
    · tauto
    · intro hv
      exact ⟨hBE hv,fun h => h.2 hv⟩
  have hsub := RegionSSA.conditional_entropy_antitone hq Ω (E\B) (E\B) E
    (Finset.Subset.refl _) Finset.sdiff_subset
  rw [hdiff,Finset.sdiff_self,vonNeumannEntropy_empty Ω hΩ,sub_zero] at hsub
  have hparts := PolynomialPEPS.SubvolumeTiling.tiles_subadditive (vonNeumannEntropy Ω)
    (vonNeumannEntropy_empty Ω hΩ) (RegionSSA.conditional_entropy_antitone hq Ω)
    (tile (L:=L) (M:=n/r) lo₁ lo₂ r) Finset.univ
    (fun i _ j _ hij => tiles_disjoint lo₁ lo₂ r hr i j hij)
  dsimp only [PolynomialPEPS.SubvolumeTiling.unionTiles] at hparts
  rw [tiles_cover lo₁ lo₂ r hr] at hparts
  have hsum := Finset.sum_le_sum (fun (i : Index (n/r)) (_ : i∈Finset.univ) => hF i)
  simp only [Finset.sum_const,Finset.card_univ,Index,Fintype.card_prod,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] at hsum
  have hfull : vonNeumannEntropy Ω B≤((n/r:ℕ):ℝ)^2*F := by
    simpa only [pow_two] using hparts.trans hsum
  have hrem := vonNeumannEntropy_le_card_log hq Ω hΩ (E\B)
  have hc : ((E\B).card:ℝ)≤2*(n:ℝ)*(r:ℝ) := by
    dsimp only [E,B]
    exact_mod_cast box_remainder_card (L:=L) lo₁ lo₂ n r hr
  have hQ : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have herr := hrem.trans (mul_le_mul_of_nonneg_right hc hQ)
  change vonNeumannEntropy Ω E≤_
  linarith only [hsub,hfull,herr]

theorem square_entropy_below_scale (hq : 0<q) (J Δ E₀ : ℝ)
    (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hΩ : ‖Ω‖=1) (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (k n : ℕ) (lo₁ lo₂ : ℤ)
    (hn : n≤(4*(2^(blocks q J Δ)+1))^(2*k)) :
    let M : ℕ := 4*(2^(blocks q J Δ)+1)
    let R := (M:ℝ)^2-2
    vonNeumannEntropy Ω (box lo₁ lo₂ 1 n) ≤
      (3*Real.log q+4*bufferConstant q J Δ)*((M:ℝ)^2*R)^k := by
  let M : ℕ := 4*(2^(blocks q J Δ)+1)
  let R : ℝ := (M:ℝ)^2-2
  let A := Real.log q+4*bufferConstant q J Δ
  let r := M^k
  have hM : (4:ℝ)≤M := by
    dsimp only [M]
    exact_mod_cast (Nat.mul_le_mul_left 4 (Nat.succ_le_succ (Nat.zero_le (2^(blocks q J Δ)))))
  have hM0 : 0<(M:ℝ) := (by norm_num : (0:ℝ)<4).trans_le hM
  have hMn : 0<M := by exact_mod_cast hM0
  have hR : (M:ℝ)≤R := by dsimp only [R]; nlinarith only [hM]
  have hR0 : 0≤R := (le_of_lt hM0).trans hR
  have hr : 0<r := pow_pos hMn k
  have hr0 : 0≤(r:ℝ) := Nat.cast_nonneg _
  have hQ : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hA : 0≤A := by dsimp only [A,bufferConstant]; positivity
  have hnr : n≤r*r := by
    change n≤M^(2*k) at hn
    simpa only [r,← pow_add,two_mul] using hn
  have hdiv : n/r≤r := by
    have hh := Nat.div_le_div_right (c:=r) hnr
    simpa only [Nat.mul_div_cancel _ hr] using hh
  have hf : ∀ i : Index (n/r), vonNeumannEntropy Ω (tile lo₁ lo₂ r i)≤A*R^k := by
    intro i
    rw [tile_as_box]
    exact square_scale_entropy hq J Δ E₀ hJ hΔ hv he Ω hΩ hH hg hgap k _ _
  have hh := entropy_square_tiling_bound hq Ω hΩ lo₁ lo₂ n r hr (A*R^k) hf
  have hp : (r:ℝ)≤R^k := by
    dsimp only [r]
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (le_of_lt hM0) hR k
  have ht : (r:ℝ)^2*R^k=((M:ℝ)^2*R)^k := by
    rw [mul_pow]
    congr 1
    dsimp only [r]
    push_cast
    rw [← pow_mul,← pow_mul,Nat.mul_comm k 2]
  have hD : ((n/r:ℕ):ℝ)^2≤(r:ℝ)^2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdiv) 2
  have hN : (n:ℝ)≤(r:ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hnr
  have h1 := mul_le_mul_of_nonneg_right hD (mul_nonneg hA (pow_nonneg hR0 k))
  have h2 := mul_le_mul_of_nonneg_right hN (mul_nonneg hr0 hQ)
  have h3 := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (sq_nonneg (r:ℝ)) hQ)
  change vonNeumannEntropy Ω (box lo₁ lo₂ 1 n)≤
    (3*Real.log q+4*bufferConstant q J Δ)*((M:ℝ)^2*R)^k
  calc
    _ ≤ (r:ℝ)^2*(A*R^k)+2*((r:ℝ)^2*R^k)*Real.log q := by
      nlinarith only [hh,h1,h2,h3]
    _ = (A+2*Real.log q)*((M:ℝ)^2*R)^k := by rw [← ht]; ring
    _ = _ := by dsimp only [A]; ring

end PolynomialPEPS.Subvolume.RectangleTiling

end

end OAI
