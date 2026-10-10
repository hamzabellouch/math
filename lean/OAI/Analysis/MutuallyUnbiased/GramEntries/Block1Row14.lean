import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block44
import OAI.Analysis.MutuallyUnbiased.GramRows.Block45
import OAI.Analysis.MutuallyUnbiased.GramRows.Block46
import OAI.Analysis.MutuallyUnbiased.GramRows.Block47

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2672, row2673, row2674, row2675, row2676, row2677, row2678, row2679, row2680, row2681, row2682, row2683, row2684, row2685, row2686, row2687, row2688, row2689, row2690, row2691, row2692, row2693, row2694, row2695]

theorem entryCheck14_0 : entry14_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_0 k)) := by decide +kernel

theorem rowsSound14_0 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval2672 x
  · exact rowEval2673 x
  · exact rowEval2674 x
  · exact rowEval2675 x
  · exact rowEval2676 x
  · exact rowEval2677 x
  · exact rowEval2678 x
  · exact rowEval2679 x
  · exact rowEval2680 x
  · exact rowEval2681 x
  · exact rowEval2682 x
  · exact rowEval2683 x
  · exact rowEval2684 x
  · exact rowEval2685 x
  · exact rowEval2686 x
  · exact rowEval2687 x
  · exact rowEval2688 x
  · exact rowEval2689 x
  · exact rowEval2690 x
  · exact rowEval2691 x
  · exact rowEval2692 x
  · exact rowEval2693 x
  · exact rowEval2694 x
  · exact rowEval2695 x

theorem entryEval14_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_0 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck14_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_0]

def rows14_1 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2696, row2697, row2698, row2699, row2700, row2701, row2702, row2703, row2704, row2705, row2706, row2707, row2708, row2709, row2710, row2711, row2712, row2713, row2714, row2715, row2716, row2717, row2718, row2719]

theorem entryCheck14_1 : entry14_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_1 k)) := by decide +kernel

theorem rowsSound14_1 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval2696 x
  · exact rowEval2697 x
  · exact rowEval2698 x
  · exact rowEval2699 x
  · exact rowEval2700 x
  · exact rowEval2701 x
  · exact rowEval2702 x
  · exact rowEval2703 x
  · exact rowEval2704 x
  · exact rowEval2705 x
  · exact rowEval2706 x
  · exact rowEval2707 x
  · exact rowEval2708 x
  · exact rowEval2709 x
  · exact rowEval2710 x
  · exact rowEval2711 x
  · exact rowEval2712 x
  · exact rowEval2713 x
  · exact rowEval2714 x
  · exact rowEval2715 x
  · exact rowEval2716 x
  · exact rowEval2717 x
  · exact rowEval2718 x
  · exact rowEval2719 x

theorem entryEval14_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_1 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck14_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_1]

def rows14_2 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2720, row2721, row2722, row2723, row2724, row2725, row2726, row2727, row2728, row2729, row2730, row2731, row2732, row2733, row2734, row2735, row2736, row2737, row2738, row2739, row2740, row2741, row2742, row2743]

theorem entryCheck14_2 : entry14_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_2 k)) := by decide +kernel

theorem rowsSound14_2 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval2720 x
  · exact rowEval2721 x
  · exact rowEval2722 x
  · exact rowEval2723 x
  · exact rowEval2724 x
  · exact rowEval2725 x
  · exact rowEval2726 x
  · exact rowEval2727 x
  · exact rowEval2728 x
  · exact rowEval2729 x
  · exact rowEval2730 x
  · exact rowEval2731 x
  · exact rowEval2732 x
  · exact rowEval2733 x
  · exact rowEval2734 x
  · exact rowEval2735 x
  · exact rowEval2736 x
  · exact rowEval2737 x
  · exact rowEval2738 x
  · exact rowEval2739 x
  · exact rowEval2740 x
  · exact rowEval2741 x
  · exact rowEval2742 x
  · exact rowEval2743 x

theorem entryEval14_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_2 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck14_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_2]

def rows14_3 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2744, row2745, row2746, row2747, row2748, row2749, row2750, row2751, row2752, row2753, row2754, row2755, row2756, row2757, row2758, row2759, row2760, row2761, row2762, row2763, row2764, row2765, row2766, row2767]

theorem entryCheck14_3 : entry14_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_3 k)) := by decide +kernel

theorem rowsSound14_3 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval2744 x
  · exact rowEval2745 x
  · exact rowEval2746 x
  · exact rowEval2747 x
  · exact rowEval2748 x
  · exact rowEval2749 x
  · exact rowEval2750 x
  · exact rowEval2751 x
  · exact rowEval2752 x
  · exact rowEval2753 x
  · exact rowEval2754 x
  · exact rowEval2755 x
  · exact rowEval2756 x
  · exact rowEval2757 x
  · exact rowEval2758 x
  · exact rowEval2759 x
  · exact rowEval2760 x
  · exact rowEval2761 x
  · exact rowEval2762 x
  · exact rowEval2763 x
  · exact rowEval2764 x
  · exact rowEval2765 x
  · exact rowEval2766 x
  · exact rowEval2767 x

theorem entryEval14_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_3 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck14_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_3]

def rows14_4 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2768, row2769, row2770, row2771, row2772, row2773, row2774, row2775, row2776, row2777, row2778, row2779, row2780, row2781, row2782, row2783, row2784, row2785, row2786, row2787, row2788, row2789, row2790, row2791]

theorem entryCheck14_4 : entry14_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_4 k)) := by decide +kernel

theorem rowsSound14_4 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval2768 x
  · exact rowEval2769 x
  · exact rowEval2770 x
  · exact rowEval2771 x
  · exact rowEval2772 x
  · exact rowEval2773 x
  · exact rowEval2774 x
  · exact rowEval2775 x
  · exact rowEval2776 x
  · exact rowEval2777 x
  · exact rowEval2778 x
  · exact rowEval2779 x
  · exact rowEval2780 x
  · exact rowEval2781 x
  · exact rowEval2782 x
  · exact rowEval2783 x
  · exact rowEval2784 x
  · exact rowEval2785 x
  · exact rowEval2786 x
  · exact rowEval2787 x
  · exact rowEval2788 x
  · exact rowEval2789 x
  · exact rowEval2790 x
  · exact rowEval2791 x

theorem entryEval14_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_4 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck14_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_4]

def rows14_5 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2792, row2793, row2794, row2795, row2796, row2797, row2798, row2799, row2800, row2801, row2802, row2803, row2804, row2805, row2806, row2807, row2808, row2809, row2810, row2811, row2812, row2813, row2814, row2815]

theorem entryCheck14_5 : entry14_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_5 k)) := by decide +kernel

theorem rowsSound14_5 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval2792 x
  · exact rowEval2793 x
  · exact rowEval2794 x
  · exact rowEval2795 x
  · exact rowEval2796 x
  · exact rowEval2797 x
  · exact rowEval2798 x
  · exact rowEval2799 x
  · exact rowEval2800 x
  · exact rowEval2801 x
  · exact rowEval2802 x
  · exact rowEval2803 x
  · exact rowEval2804 x
  · exact rowEval2805 x
  · exact rowEval2806 x
  · exact rowEval2807 x
  · exact rowEval2808 x
  · exact rowEval2809 x
  · exact rowEval2810 x
  · exact rowEval2811 x
  · exact rowEval2812 x
  · exact rowEval2813 x
  · exact rowEval2814 x
  · exact rowEval2815 x

theorem entryEval14_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_5 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck14_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_5]

def rows14_6 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2816, row2817, row2818, row2819, row2820, row2821, row2822, row2823, row2824, row2825, row2826, row2827, row2828, row2829, row2830, row2831, row2832, row2833, row2834, row2835, row2836, row2837, row2838, row2839]

theorem entryCheck14_6 : entry14_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_6 k)) := by decide +kernel

theorem rowsSound14_6 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2816 x
  · exact rowEval2817 x
  · exact rowEval2818 x
  · exact rowEval2819 x
  · exact rowEval2820 x
  · exact rowEval2821 x
  · exact rowEval2822 x
  · exact rowEval2823 x
  · exact rowEval2824 x
  · exact rowEval2825 x
  · exact rowEval2826 x
  · exact rowEval2827 x
  · exact rowEval2828 x
  · exact rowEval2829 x
  · exact rowEval2830 x
  · exact rowEval2831 x
  · exact rowEval2832 x
  · exact rowEval2833 x
  · exact rowEval2834 x
  · exact rowEval2835 x
  · exact rowEval2836 x
  · exact rowEval2837 x
  · exact rowEval2838 x
  · exact rowEval2839 x

theorem entryEval14_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_6 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck14_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_6]

def rows14_7 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2840, row2841, row2842, row2843, row2844, row2845, row2846, row2847, row2848, row2849, row2850, row2851, row2852, row2853, row2854, row2855, row2856, row2857, row2858, row2859, row2860, row2861, row2862, row2863]

theorem entryCheck14_7 : entry14_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_7 k)) := by decide +kernel

theorem rowsSound14_7 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2840 x
  · exact rowEval2841 x
  · exact rowEval2842 x
  · exact rowEval2843 x
  · exact rowEval2844 x
  · exact rowEval2845 x
  · exact rowEval2846 x
  · exact rowEval2847 x
  · exact rowEval2848 x
  · exact rowEval2849 x
  · exact rowEval2850 x
  · exact rowEval2851 x
  · exact rowEval2852 x
  · exact rowEval2853 x
  · exact rowEval2854 x
  · exact rowEval2855 x
  · exact rowEval2856 x
  · exact rowEval2857 x
  · exact rowEval2858 x
  · exact rowEval2859 x
  · exact rowEval2860 x
  · exact rowEval2861 x
  · exact rowEval2862 x
  · exact rowEval2863 x

theorem entryEval14_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_7 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck14_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_7]

def rows14_8 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2864, row2865, row2866, row2867, row2868, row2869, row2870, row2871, row2872, row2873, row2874, row2875, row2876, row2877, row2878, row2879, row2880, row2881, row2882, row2883, row2884, row2885, row2886, row2887]

theorem entryCheck14_8 : entry14_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_8 k)) := by decide +kernel

theorem rowsSound14_8 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2864 x
  · exact rowEval2865 x
  · exact rowEval2866 x
  · exact rowEval2867 x
  · exact rowEval2868 x
  · exact rowEval2869 x
  · exact rowEval2870 x
  · exact rowEval2871 x
  · exact rowEval2872 x
  · exact rowEval2873 x
  · exact rowEval2874 x
  · exact rowEval2875 x
  · exact rowEval2876 x
  · exact rowEval2877 x
  · exact rowEval2878 x
  · exact rowEval2879 x
  · exact rowEval2880 x
  · exact rowEval2881 x
  · exact rowEval2882 x
  · exact rowEval2883 x
  · exact rowEval2884 x
  · exact rowEval2885 x
  · exact rowEval2886 x
  · exact rowEval2887 x

theorem entryEval14_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_8 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck14_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_8]

def rows14_9 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2888, row2889, row2890, row2891, row2892, row2893, row2894, row2895, row2896, row2897, row2898, row2899, row2900, row2901, row2902, row2903, row2904, row2905, row2906, row2907, row2908, row2909, row2910, row2911]

theorem entryCheck14_9 : entry14_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_9 k)) := by decide +kernel

theorem rowsSound14_9 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2888 x
  · exact rowEval2889 x
  · exact rowEval2890 x
  · exact rowEval2891 x
  · exact rowEval2892 x
  · exact rowEval2893 x
  · exact rowEval2894 x
  · exact rowEval2895 x
  · exact rowEval2896 x
  · exact rowEval2897 x
  · exact rowEval2898 x
  · exact rowEval2899 x
  · exact rowEval2900 x
  · exact rowEval2901 x
  · exact rowEval2902 x
  · exact rowEval2903 x
  · exact rowEval2904 x
  · exact rowEval2905 x
  · exact rowEval2906 x
  · exact rowEval2907 x
  · exact rowEval2908 x
  · exact rowEval2909 x
  · exact rowEval2910 x
  · exact rowEval2911 x

theorem entryEval14_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_9 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck14_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_9]

def rows14_10 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2912, row2913, row2914, row2915, row2916, row2917, row2918, row2919, row2920, row2921, row2922, row2923, row2924, row2925, row2926, row2927, row2928, row2929, row2930, row2931, row2932, row2933, row2934, row2935]

theorem entryCheck14_10 : entry14_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_10 k)) := by decide +kernel

theorem rowsSound14_10 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2912 x
  · exact rowEval2913 x
  · exact rowEval2914 x
  · exact rowEval2915 x
  · exact rowEval2916 x
  · exact rowEval2917 x
  · exact rowEval2918 x
  · exact rowEval2919 x
  · exact rowEval2920 x
  · exact rowEval2921 x
  · exact rowEval2922 x
  · exact rowEval2923 x
  · exact rowEval2924 x
  · exact rowEval2925 x
  · exact rowEval2926 x
  · exact rowEval2927 x
  · exact rowEval2928 x
  · exact rowEval2929 x
  · exact rowEval2930 x
  · exact rowEval2931 x
  · exact rowEval2932 x
  · exact rowEval2933 x
  · exact rowEval2934 x
  · exact rowEval2935 x

theorem entryEval14_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_10 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck14_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_10]

def rows14_11 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2936, row2937, row2938, row2939, row2940, row2941, row2942, row2943, row2944, row2945, row2946, row2947, row2948, row2949, row2950, row2951, row2952, row2953, row2954, row2955, row2956, row2957, row2958, row2959]

theorem entryCheck14_11 : entry14_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_11 k)) := by decide +kernel

theorem rowsSound14_11 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2936 x
  · exact rowEval2937 x
  · exact rowEval2938 x
  · exact rowEval2939 x
  · exact rowEval2940 x
  · exact rowEval2941 x
  · exact rowEval2942 x
  · exact rowEval2943 x
  · exact rowEval2944 x
  · exact rowEval2945 x
  · exact rowEval2946 x
  · exact rowEval2947 x
  · exact rowEval2948 x
  · exact rowEval2949 x
  · exact rowEval2950 x
  · exact rowEval2951 x
  · exact rowEval2952 x
  · exact rowEval2953 x
  · exact rowEval2954 x
  · exact rowEval2955 x
  · exact rowEval2956 x
  · exact rowEval2957 x
  · exact rowEval2958 x
  · exact rowEval2959 x

theorem entryEval14_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_11 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck14_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_11]

def rows14_12 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2960, row2961, row2962, row2963, row2964, row2965, row2966, row2967, row2968, row2969, row2970, row2971, row2972, row2973, row2974, row2975, row2976, row2977, row2978, row2979, row2980, row2981, row2982, row2983]

theorem entryCheck14_12 : entry14_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_12 k)) := by decide +kernel

theorem rowsSound14_12 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form12) x := by
  fin_cases k
  · exact rowEval2960 x
  · exact rowEval2961 x
  · exact rowEval2962 x
  · exact rowEval2963 x
  · exact rowEval2964 x
  · exact rowEval2965 x
  · exact rowEval2966 x
  · exact rowEval2967 x
  · exact rowEval2968 x
  · exact rowEval2969 x
  · exact rowEval2970 x
  · exact rowEval2971 x
  · exact rowEval2972 x
  · exact rowEval2973 x
  · exact rowEval2974 x
  · exact rowEval2975 x
  · exact rowEval2976 x
  · exact rowEval2977 x
  · exact rowEval2978 x
  · exact rowEval2979 x
  · exact rowEval2980 x
  · exact rowEval2981 x
  · exact rowEval2982 x
  · exact rowEval2983 x

theorem entryEval14_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_12 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form12 B := by
  rw [entryCheck14_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_12]

def rows14_13 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2984, row2985, row2986, row2987, row2988, row2989, row2990, row2991, row2992, row2993, row2994, row2995, row2996, row2997, row2998, row2999, row3000, row3001, row3002, row3003, row3004, row3005, row3006, row3007]

theorem entryCheck14_13 : entry14_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_13 k)) := by decide +kernel

theorem rowsSound14_13 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form13) x := by
  fin_cases k
  · exact rowEval2984 x
  · exact rowEval2985 x
  · exact rowEval2986 x
  · exact rowEval2987 x
  · exact rowEval2988 x
  · exact rowEval2989 x
  · exact rowEval2990 x
  · exact rowEval2991 x
  · exact rowEval2992 x
  · exact rowEval2993 x
  · exact rowEval2994 x
  · exact rowEval2995 x
  · exact rowEval2996 x
  · exact rowEval2997 x
  · exact rowEval2998 x
  · exact rowEval2999 x
  · exact rowEval3000 x
  · exact rowEval3001 x
  · exact rowEval3002 x
  · exact rowEval3003 x
  · exact rowEval3004 x
  · exact rowEval3005 x
  · exact rowEval3006 x
  · exact rowEval3007 x

theorem entryEval14_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_13 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form13 B := by
  rw [entryCheck14_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_13]

def rows14_14 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row3008, row3009, row3010, row3011, row3012, row3013, row3014, row3015, row3016, row3017, row3018, row3019, row3020, row3021, row3022, row3023, row3024, row3025, row3026, row3027, row3028, row3029, row3030, row3031]

theorem entryCheck14_14 : entry14_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form14.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form14.terms k).coefficient) (rows14_14 k)) := by decide +kernel

theorem rowsSound14_14 (k : Fin GramFunctions.Block1.form14.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows14_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form14.terms k).tag (GramFunctions.Block1.form14.terms k).charge GramFunctions.Block1.form14) x := by
  fin_cases k
  · exact rowEval3008 x
  · exact rowEval3009 x
  · exact rowEval3010 x
  · exact rowEval3011 x
  · exact rowEval3012 x
  · exact rowEval3013 x
  · exact rowEval3014 x
  · exact rowEval3015 x
  · exact rowEval3016 x
  · exact rowEval3017 x
  · exact rowEval3018 x
  · exact rowEval3019 x
  · exact rowEval3020 x
  · exact rowEval3021 x
  · exact rowEval3022 x
  · exact rowEval3023 x
  · exact rowEval3024 x
  · exact rowEval3025 x
  · exact rowEval3026 x
  · exact rowEval3027 x
  · exact rowEval3028 x
  · exact rowEval3029 x
  · exact rowEval3030 x
  · exact rowEval3031 x

theorem entryEval14_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry14_14 (GramNormalization.eval B) = GramFunctions.Block1.form14.mixedGram GramFunctions.Block1.form14 B := by
  rw [entryCheck14_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form14 GramFunctions.Block1.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound14_14]

end MUB6.Certificate.GramEntries.Block1

end OAI
