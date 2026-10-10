import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} {τ : A →ₚ[ℂ] ℂ} {S : ι → StarSubalgebra ℂ A}

variable {i j : ι}

omit [StarOrderedRing A] in
theorem free_centered_two (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b : A} (ha : a ∈ S i) (hb : b ∈ S j) (hta : τ a = 0) (htb : τ b = 0) :
    τ (a*b) = 0 := by
  have hz := hfree [(i,a),(j,b)] (by simp) (by simpa using hij)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨‹_›,‹_›⟩)
  simpa using hz

omit [StarOrderedRing A] in
theorem free_centered_four (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b c d : A} (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (hta : τ a = 0) (htb : τ b = 0) (htc : τ c = 0) (htd : τ d = 0) :
    τ (a*b*c*d) = 0 := by
  have hz := hfree [(i,a),(j,b),(i,c),(j,d)] (by simp)
    (by simp [List.isChain_cons, hij, hij.symm])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨‹_›,‹_›⟩)
  simpa [mul_assoc] using hz

omit [StarOrderedRing A] in
theorem free_centered_six (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b c d e f : A} (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (he : e ∈ S i) (hf : f ∈ S j)
    (hta : τ a = 0) (htb : τ b = 0) (htc : τ c = 0) (htd : τ d = 0)
    (hte : τ e = 0) (htf : τ f = 0) : τ (a*b*c*d*e*f) = 0 := by
  have hz := hfree [(i,a),(j,b),(i,c),(j,d),(i,e),(j,f)] (by simp)
    (by simp [List.isChain_cons, hij, hij.symm])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨‹_›,‹_›⟩)
  simpa [mul_assoc] using hz

omit [StarOrderedRing A] in
theorem free_centered_eight (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b c d e f g h : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (he : e ∈ S i) (hf : f ∈ S j) (hg : g ∈ S i) (hh : h ∈ S j)
    (hta : τ a = 0) (htb : τ b = 0) (htc : τ c = 0) (htd : τ d = 0)
    (hte : τ e = 0) (htf : τ f = 0) (htg : τ g = 0) (hth : τ h = 0) :
    τ (a*b*c*d*e*f*g*h) = 0 := by
  have hz := hfree [(i,a),(j,b),(i,c),(j,d),(i,e),(j,f),(i,g),(j,h)] (by simp)
    (by simp [List.isChain_cons, hij, hij.symm])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨‹_›,‹_›⟩)
  simpa [mul_assoc] using hz

omit [StarOrderedRing A] in
theorem free_trace_pair (hτ : τ 1 = 1) (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b : A} (ha : a ∈ S i) (hb : b ∈ S j) : τ (a*b) = τ a * τ b := by
  have hc (x : A) : τ (x - τ x • (1:A)) = 0 := by simp [map_sub,map_smul,hτ]
  have hz := free_centered_two hfree hij
    ((S i).sub_mem ha ((S i).smul_mem (S i).one_mem (τ a)))
    ((S j).sub_mem hb ((S j).smul_mem (S j).one_mem (τ b))) (hc a) (hc b)
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
    map_sub,map_smul,smul_eq_mul,hτ,mul_one] at hz
  linear_combination hz

omit [StarOrderedRing A] in
theorem free_trace_four (hτ : FaithfulTracial τ) (hfree : ScalarFree τ S) (hij : i ≠ j)
    {a b c d : A} (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (hta : τ a = 0) (htc : τ c = 0) :
    τ (a*b*c*d) = τ (a*c) * τ b * τ d := by
  have cen (x : A) : τ (x - τ x • (1:A)) = 0 := by simp [map_sub,map_smul,hτ.1]
  have hz := free_centered_four hfree hij ha
    ((S j).sub_mem hb ((S j).smul_mem (S j).one_mem (τ b))) hc
    ((S j).sub_mem hd ((S j).smul_mem (S j).one_mem (τ d))) hta (cen b) htc (cen d)
  have h1 : τ (a*c*d) = τ (a*c) * τ d := free_trace_pair hτ.1 hfree hij ((S i).mul_mem ha hc) hd
  have h2 : τ (a*b*c) = τ (a*c) * τ b := by
    rw [hτ.2.1 (a*b) c, ← mul_assoc, free_trace_pair hτ.1 hfree hij ((S i).mul_mem hc ha) hb,
      hτ.2.1 c a]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,mul_one,
    map_sub,map_smul,smul_eq_mul] at hz
  rw [h1,h2] at hz
  linear_combination hz

omit [StarOrderedRing A] in
theorem free_trace_six_partial (hτ : FaithfulTracial τ)
    (hfree : ScalarFree τ S) (hij : i ≠ j)
    {q a b c : A} (hq : q ∈ S j) (htq : τ q = 0)
    (ha : a ∈ S i) (hb : b ∈ S i) (hc : c ∈ S i)
    (hta : τ a = 0) (htb : τ b = 0) : τ (q*a*q*b*q*c) = 0 := by
  have h0 : τ (q*a*q*b*q) = 0 := by
    calc τ (q*a*q*b*q) = τ (a*q*b*(q*q)) := by
            simpa only [mul_assoc] using hτ.2.1 q (a*q*b*q)
      _ = 0 := by rw [free_trace_four hτ hfree hij ha hq hb ((S j).mul_mem hq hq) hta htb,htq]; simp
  have hz := free_centered_six hfree hij.symm hq ha hq hb hq
    ((S i).sub_mem hc ((S i).smul_mem (S i).one_mem (τ c))) htq hta htq htb htq
    (by simp [map_sub,map_smul,hτ.1])
  simpa only [mul_sub,mul_smul_comm,mul_one,map_sub,map_smul,smul_eq_mul,h0,mul_zero,
    sub_zero] using hz

omit [StarOrderedRing A] in
theorem free_compression_four (hτ : FaithfulTracial τ)
    (hfree : ScalarFree τ S) (hij : i ≠ j)
    {p a b c d : A} (hp : p ∈ S j)
    (ha : a ∈ S i) (hb : b ∈ S i) (hc : c ∈ S i) (hd : d ∈ S i)
    (hta : τ a = 0) (htb : τ b = 0) (htc : τ c = 0) (htd : τ d = 0) :
    τ (p*a*p*b*p*c*p*d) =
      (τ p)^4 * τ (a*b*c*d) + (τ p)^2 * (τ (p*p) - (τ p)^2) *
        (τ (a*b)*τ (c*d) + τ (b*c)*τ (d*a)) := by
  let q := p - τ p • (1:A)
  have hq : q ∈ S j := (S j).sub_mem hp ((S j).smul_mem (S j).one_mem (τ p))
  have htq : τ q = 0 := by simp [q,map_sub,map_smul,hτ.1]
  have hqq : τ (q*q) = τ (p*p) - (τ p)^2 := by
    simp only [q,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      map_sub,map_smul,smul_eq_mul,hτ.1,mul_one]
    ring
  have h1 (x : A) (hx : x ∈ S i) : τ (q*x) = 0 := by
    rw [free_trace_pair hτ.1 hfree hij.symm hq hx, htq,zero_mul]
  have h2 (x y : A) (hx : x ∈ S i) (hy : y ∈ S i) :
      τ (q*x*q*y) = τ (q*q) * τ x * τ y :=
    free_trace_four hτ hfree hij.symm hq hx hq hy htq htq
  have h31 : τ (q*a*q*b*q*c*d) = 0 := by
    simpa only [mul_assoc] using free_trace_six_partial hτ hfree hij hq htq ha hb
      ((S i).mul_mem hc hd) hta htb
  have h32 : τ (q*a*q*b*c*q*d) = 0 := by
    calc τ (q*a*q*b*c*q*d) = τ (q*d*q*a*q*(b*c)) := by
            simpa only [mul_assoc] using hτ.2.1 (q*a*q*b*c) (q*d)
      _ = 0 := free_trace_six_partial hτ hfree hij hq htq hd ha
         ((S i).mul_mem hb hc) htd hta
  have h33 : τ (q*a*b*q*c*q*d) = 0 := by
    calc τ (q*a*b*q*c*q*d) = τ (q*c*q*d*q*(a*b)) := by
            simpa only [mul_assoc] using hτ.2.1 (q*a*b) (q*c*q*d)
      _ = 0 := free_trace_six_partial hτ hfree hij hq htq hc hd
         ((S i).mul_mem ha hb) htc htd
  have h34 : τ (a*q*b*q*c*q*d) = 0 := by
    calc τ (a*q*b*q*c*q*d) = τ (q*b*q*c*q*(d*a)) := by
            simpa only [mul_assoc] using hτ.2.1 a (q*b*q*c*q*d)
      _ = 0 := free_trace_six_partial hτ hfree hij hq htq hb hc
         ((S i).mul_mem hd ha) htb htc
  have h4 : τ (q*a*q*b*q*c*q*d) = 0 :=
    free_centered_eight hfree hij.symm hq ha hq hb hq hc hq hd
      htq hta htq htb htq htc htq htd
  have h11 : τ (q*a*b*c*d) = 0 := by
    simpa only [mul_assoc] using h1 (a*b*c*d)
      ((S i).mul_mem ((S i).mul_mem ((S i).mul_mem ha hb) hc) hd)
  have h12 : τ (a*q*b*c*d) = 0 := by
    calc τ (a*q*b*c*d) = τ (q*(b*c*d*a)) := by
            simpa only [mul_assoc] using hτ.2.1 a (q*b*c*d)
      _ = 0 := h1 _ ((S i).mul_mem ((S i).mul_mem ((S i).mul_mem hb hc) hd) ha)
  have h13 : τ (a*b*q*c*d) = 0 := by
    calc τ (a*b*q*c*d) = τ (q*(c*d*a*b)) := by
            simpa only [mul_assoc] using hτ.2.1 (a*b) (q*c*d)
      _ = 0 := h1 _ ((S i).mul_mem ((S i).mul_mem ((S i).mul_mem hc hd) ha) hb)
  have h14 : τ (a*b*c*q*d) = 0 := by
    calc τ (a*b*c*q*d) = τ (q*(d*a*b*c)) := by
            simpa only [mul_assoc] using hτ.2.1 (a*b*c) (q*d)
      _ = 0 := h1 _ ((S i).mul_mem ((S i).mul_mem ((S i).mul_mem hd ha) hb) hc)
  have h21 : τ (q*a*q*b*c*d) = 0 := by
    have hz := h2 a (b*c*d) ha ((S i).mul_mem ((S i).mul_mem hb hc) hd)
    simpa only [mul_assoc,hta,mul_zero,zero_mul] using hz
  have h22 : τ (q*a*b*q*c*d) = τ (q*q) * τ (a*b) * τ (c*d) := by
    simpa only [mul_assoc] using h2 (a*b) (c*d) ((S i).mul_mem ha hb) ((S i).mul_mem hc hd)
  have h23 : τ (q*a*b*c*q*d) = 0 := by
    have hz := h2 (a*b*c) d ((S i).mul_mem ((S i).mul_mem ha hb) hc) hd
    simpa only [mul_assoc,htd,mul_zero] using hz
  have h24 : τ (a*q*b*q*c*d) = 0 := by
    calc τ (a*q*b*q*c*d) = τ (q*b*q*(c*d*a)) := by
            simpa only [mul_assoc] using hτ.2.1 a (q*b*q*c*d)
      _ = 0 := by rw [h2 b (c*d*a) hb
        ((S i).mul_mem ((S i).mul_mem hc hd) ha),htb]; simp
  have h25 : τ (a*q*b*c*q*d) = τ (q*q) * τ (b*c) * τ (d*a) := by
    calc τ (a*q*b*c*q*d) = τ (q*(b*c)*q*(d*a)) := by
            simpa only [mul_assoc] using hτ.2.1 a (q*b*c*q*d)
      _ = _ := h2 (b*c) (d*a) ((S i).mul_mem hb hc) ((S i).mul_mem hd ha)
  have h26 : τ (a*b*q*c*q*d) = 0 := by
    calc τ (a*b*q*c*q*d) = τ (q*c*q*(d*a*b)) := by
            simpa only [mul_assoc] using hτ.2.1 (a*b) (q*c*q*d)
      _ = 0 := by rw [h2 c (d*a*b) hc
        ((S i).mul_mem ((S i).mul_mem hd ha) hb),htc]; simp
  have hpq : p = q + τ p • (1:A) := by simp [q]
  conv_lhs => rw [hpq]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
    map_add,map_smul,smul_eq_mul]
  rw [h4,h31,h32,h33,h34,h11,h12,h13,h14,h21,h22,h23,h24,h25,h26,hqq]
  ring

theorem trace_star (x : A) : τ (star x) = star (τ x) := by
  have h := inner_conj_symm (𝕜 := ℂ) (τ.toPreGNS x) (τ.toPreGNS 1)
  simpa only [PositiveLinearMap.preGNS_inner_def,star_one,one_mul,mul_one,
    PositiveLinearMap.ofPreGNS_toPreGNS, Complex.star_def] using h.symm

theorem projection_compression_second (hτ : FaithfulTracial τ)
    (hfree : ScalarFree τ S) (hij : i ≠ j)
    {p a : A} (hp : p ∈ S j) (hps : star p = p) (hpp : p*p = p)
    (ha : a ∈ S i) (hta : τ a = 0) :
    τ ((p*a*p)*star (p*a*p)) = (τ p)^2 * τ (a*star a) := by
  have hp' (x : A) : p*(p*x) = p*x := by rw [← mul_assoc,hpp]
  have he : (p*a*p)*star (p*a*p) = p*a*p*star a*p := by
    simp only [star_mul,hps,mul_assoc,hp']
  rw [he,hτ.2.1 (p*a*p*star a) p]
  simp only [mul_assoc,hp']
  have hz := free_trace_four hτ hfree hij ha hp (star_mem ha) hp hta (by rw [trace_star,hta]; simp)
  calc τ (p*(a*(p*star a))) = τ (a*p*star a*p) := by
          simpa only [mul_assoc] using hτ.2.1 p (a*p*star a)
    _ = _ := by rw [hz]; ring

theorem projection_compression_fourth (hτ : FaithfulTracial τ)
    (hfree : ScalarFree τ S) (hij : i ≠ j)
    {p a : A} (hp : p ∈ S j) (hps : star p = p) (hpp : p*p = p)
    (ha : a ∈ S i) (hta : τ a = 0) :
    τ (((p*a*p)*star (p*a*p))^2) =
      (τ p)^4 * τ ((a*star a)^2) +
        2*(τ p)^3*(1-τ p)*(τ (a*star a))^2 := by
  have hp' (x : A) : p*(p*x) = p*x := by rw [← mul_assoc,hpp]
  have he : ((p*a*p)*star (p*a*p))^2 = p*a*p*star a*p*a*p*star a*p := by
    simp only [pow_two,star_mul,hps,mul_assoc,hp']
  have he' : τ (((p*a*p)*star (p*a*p))^2) = τ (p*a*p*star a*p*a*p*star a) := by
    rw [he,hτ.2.1 (p*a*p*star a*p*a*p*star a) p]
    simp only [mul_assoc,hp']
  rw [he', free_compression_four hτ hfree hij hp ha (star_mem ha) ha (star_mem ha)
    hta (by rw [trace_star,hta]; simp) hta (by rw [trace_star,hta]; simp),hpp,
    hτ.2.1 (star a) a]
  simp only [pow_two,mul_assoc]
  ring

end

end KKFreeWords
end

end OAI
